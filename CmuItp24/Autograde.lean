import Lean.Attributes

/-! A library of attributes used to mark exercises
for grading in the autograder. -/

namespace Autograde

declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := exerciseAttrStx) "exercise" str ptVal : attr

open Lean

/-- `@[exercise name pts]` marks the exercise named `name`,
indicating that it is worth `pts` pts.
For example, `@[exercise "1a" 8]`. -/
initialize exerciseAttr : ParametricAttribute (String × Float) ←
  registerParametricAttribute {
    name := `exerciseAttrStx
    descr := ""
    getParam := fun
      | _, `(attr| exercise $name:str $pts:num) =>
        return (name.getString, pts.getNat.toFloat)
      | _, `(attr| exercise $name:str $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return (name.getString, Float.ofScientific n s d)
      | _, _ => throwError "Invalid autograded exercise attribute."
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
