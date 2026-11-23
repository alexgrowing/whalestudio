import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSmul

theorem map_resTop {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop U c) = resTop V c := by
  simp only [resTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_smul : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)),
    ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  intro X L k σ c
  refine ⟨⟨fun j => resTop _ c * σ.f j, fun i j => ?_⟩, fun j => rfl⟩
  rw [map_mul, map_mul, σ.compat i j, map_resTop, map_resTop]
  ring

end GlobalTheory.SecSmul
