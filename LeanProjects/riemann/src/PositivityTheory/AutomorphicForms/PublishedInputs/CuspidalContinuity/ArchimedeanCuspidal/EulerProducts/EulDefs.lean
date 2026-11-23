import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

def xR (x : IdeleGroup ℚ) : ℝˣ := Units.map eR.toRingHom.toMonoidHom (IdeleGroup.infiniteProj wR x)

abbrev xv (v : Pl) (x : IdeleGroup ℚ) : (Qv v)ˣ := IdeleGroup.finiteProj v x

def aR (a : (InfiniteAdeleRing ℚ)ˣ) : ℝˣ :=
  Units.map (eR.toRingHom.comp (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) wR)).toMonoidHom a

end Ad3.GP
