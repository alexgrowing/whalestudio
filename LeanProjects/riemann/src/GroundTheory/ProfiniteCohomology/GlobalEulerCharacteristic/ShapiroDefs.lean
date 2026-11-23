import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

def funDiagRepresentation (X : Type*) [MulAction G X] (ρ : Representation k G V) :
    Representation k G (X → V) where
  toFun g :=
    { toFun := fun F x => ρ g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (ρ g) _ _
      map_smul' := fun c F => funext fun x => map_smul (ρ g) c _ }
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp [mul_smul]

@[simp]
theorem funDiagRepresentation_apply (X : Type*) [MulAction G X] (ρ : Representation k G V) (g : G)
    (F : X → V) (x : X) : funDiagRepresentation X ρ g F x = ρ g (F (g⁻¹ • x)) :=
  rfl

abbrev funDiagRep {k G : Type u} [CommRing k] [Group G] (X : Type u) [MulAction G X]
    (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (funDiagRepresentation X A.ρ)

end GroundTheory.ProfCoh
