import Lean.Attributes

/-! A library of attributes used to mark exercises
for grading in the autograder. -/

namespace Autograde

declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := exerciseAttrStx) "exercise" str ptVal : attr

open Lean

register_option autograde.stencil : Bool := {
  descr := "(autograde) For internal use in the autograder. Turns errors into warnings."
  defValue := false
}

def throwErrorUnlessStencil {m : Type → Type}
    [Monad m] [MonadError m] [MonadOptions m] [MonadLog m] [AddMessageContext m]
    (msg : MessageData) : m Unit := do
  if autograde.stencil.get (← getOptions) then
    Lean.logWarning msg
  else
    throwError msg

/-- `@[exercise name pts]` marks the exercise named `name`,
indicating that it is worth `pts` pts.
For example, `@[exercise "1a" 8]`. -/
initialize exerciseAttr : ParametricAttribute (String × Float) ← do
  registerParametricAttribute {
    name := `exerciseAttrStx
    descr := ""
    getParam := fun n stx => do
      if n matches .str _ "_example" then
        throwErrorUnlessStencil "Exercise solutions cannot be `example`s.\n\
          Please give the exercise a name with `theorem someName` or `def someName`."
      match stx with
      | `(attr| exercise $name:str $pts:num) =>
        return (name.getString, pts.getNat.toFloat)
      | `(attr| exercise $name:str $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return (name.getString, Float.ofScientific n s d)
      | _ => throwError "Unexpected attribute syntax '{stx}'."
  }

/-- Identify all constants marked as exercises in `env`.
For each of these, return `(constantInfo, exerciseName, exercisePts)`. -/
def getExercises (env : Environment) : Array (ConstantInfo × String × Float) := Id.run do
  let mut ret := #[]
  for (cname, exerciseName, exercisePts) in exerciseAttr.ext.getState env do
    let cinfo := env.find? cname |>.get!
    ret := ret.push (cinfo, exerciseName, exercisePts)
  return ret

end Autograde
