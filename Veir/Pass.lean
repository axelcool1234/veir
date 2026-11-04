module

public import Veir.Verifier
public import Std.Data.HashMap

/-!
  # Compilation passes

  This file contains the definition of a compilation pass type and a generic pass pipeline.
-/

namespace Veir

public section

/-- A value accepted by a pass option. -/
inductive PassOptionValue where
  | bool (value : Bool)
  | nat (value : Nat)
deriving BEq, Repr

/-- The declaration of a pass option, including its type and default value. -/
structure PassOption where
  /-- Human-readable help text for the option. -/
  description : String
  /-- The option's default value. -/
  defaultValue : PassOptionValue := .bool false

/-- The option values for one instance of a pass. -/
abbrev PassOptions := Std.HashMap String PassOptionValue

/-- Return a boolean option value, or `none` if the option is absent or has another type. -/
def PassOptions.getBool? (options : PassOptions) (name : String) : Option Bool := do
  let .bool value ← options.get? name | none
  return value

/-- Return a natural number option value, or `none` if it is absent or has another type. -/
def PassOptions.getNat? (options : PassOptions) (name : String) : Option Nat := do
  let .nat value ← options.get? name | none
  return value

/-- A compilation pass. -/
structure Pass (OpInfo : Type) [HasOpInfo OpInfo] where
  /--
    Human-readable unique identifier for the pass,
    used for registration and pipeline configuration.
  -/
  name : String
  /-- Brief explanation of what the pass does, for documentation and tooling. -/
  description : String
  /--
    The options this pass accepts, mapping each option name to its declaration.
  -/
  options : Std.HashMap String PassOption := ∅
  /--
    Execute the pass over the given IR context rooted at `op`, under the options this
    instance of the pass was given.
    Returns the context on success, or an error message on failure.
  -/
  run :
    PassOptions →
    ∀ (ctx : WfIRContext OpInfo) (op : OperationPtr),
    op.InBounds ctx.raw →
    ExceptT String IO (WfIRContext OpInfo)

/--
  Check the given option words against the options this pass accepts and return their values.
  Boolean options accept `name`, `name=true`, or `name=false`. Natural number options require
  `name=value`. Options not named take their declared default value.
-/
def Pass.parseOptions {OpInfo : Type} [HasOpInfo OpInfo]
    (pass : Pass OpInfo) (flags : List String) : Except String PassOptions := do
  let mut values : PassOptions := ∅
  for (name, option) in pass.options.toList do
    values := values.insert name option.defaultValue
  for flag in flags do
    let (name, value?) ← match flag.splitOn "=" with
      | [name] => pure (name, none)
      | [name, value] => pure (name, some value)
      | _ => throw s!"malformed option '{flag}' for pass '{pass.name}'"
    let some option := pass.options.get? name
      | let known := String.intercalate ", "
          (pass.options.keys.toArray.qsort (· < ·)).toList
        let known := if known.isEmpty then "it accepts no options" else s!"it accepts: {known}"
        throw s!"pass '{pass.name}' has no option '{name}' ({known})"
    let value ← match option.defaultValue with
      | .bool _ => match value? with
        | none | some "true" => pure (.bool true)
        | some "false" => pure (.bool false)
        | some value =>
          throw s!"invalid value '{value}' for boolean option '{name}' of pass '{pass.name}'"
      | .nat _ =>
        let some spelling := value?
          | throw s!"natural number option '{name}' of pass '{pass.name}' requires a value"
        let some value := spelling.toNat?
          | let message := s!"invalid value '{spelling}' for natural number option '{name}' " ++
              s!"of pass '{pass.name}'"
            throw message
        pure (.nat value)
    values := values.insert name value
  return values

/--
  Split one pipeline element, either `name` or `name{option1 option2 ...}`, into the name and
  the (possibly empty) list of option words.
-/
def splitPipelineElement (s : String) : Except String (String × List String) := do
  let s := s.trimAscii.toString
  match s.splitOn "{" with
  | [name] => return (name.trimAscii.toString, [])
  | [name, rest] =>
    let name := name.trimAscii.toString
    unless rest.endsWith "}" do
      throw s!"missing closing brace in the options of pass '{name}'"
    return (name, (rest.dropEnd 1).toString.splitOn " " |>.filter (!·.isEmpty))
  | _ => throw s!"unexpected nested opening brace in pipeline element '{s}'"

/-- An ordered sequence of passes to run in succession. -/
structure PassPipeline (OpInfo : Type) [HasOpInfo OpInfo] where
  /-- The ordered list of passes to run, each with the options it was given -/
  passes : Array (Pass OpInfo × PassOptions)

namespace PassPipeline

/--
  Parse a comma-separated list of pipeline elements into a `PassPipeline`, looking each
  name up in `registry`. An element is either `name` or `name{option1 option2 ...}`, where the
  boolean options use `name` or `name=true|false`, and natural number options use `name=value`.
  Returns an error if a name does not exist in the registry or an option is invalid.
-/
def ofString? {OpInfo : Type} [HasOpInfo OpInfo]
    (registry : Std.HashMap String (Pass OpInfo)) (s : String) :
    Except String (PassPipeline OpInfo) := do
  let passes ← (s.splitOn ",").mapM fun element => do
    let (name, flags) ← splitPipelineElement element
    let some pass := registry.get? name
      | throw s!"unknown pass: '{name}'"
    return (pass, ← pass.parseOptions flags)
  return { passes := passes.toArray }

/--
  Run each pass in the pipeline in order, verifying the IR after each pass.
  Returns the final context on success, or an error message on failure.
-/
def run (pipeline : PassPipeline OpCode)
    (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr)
    (disableVerifiers : Bool) :
    ExceptT String IO (WfIRContext OpCode) := do
  let mut currentCtx := ctx
  for (pass, options) in pipeline.passes do
    if h : moduleOp.InBounds currentCtx.raw then
      let ctx' ← try pass.run options currentCtx moduleOp h
                 catch errMsg => throw s!"pass '{pass.name}' failed: {errMsg}"
      if !disableVerifiers then
        if let .error errMsg := ctx'.verify moduleOp then
          throw s!"verification failed after pass '{pass.name}': {errMsg}"
      currentCtx := ctx'
    else
      throw s!"module is not in bounds before pass '{pass.name}'"
  return currentCtx

end PassPipeline

end -- public section

end Veir
