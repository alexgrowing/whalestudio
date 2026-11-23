import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val S X Z τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

theorem gs_id_appLE {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (f : Γ(X, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom f) = gs r z U f := by
  have e := gs_pull (𝟙 Z) r z U (h trivial) f
  rw [Category.id_comp] at e
  exact (gs_res (𝟙 Z) z h trivial _).trans e

theorem exists_app_eq_of_hasWt_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (W : E.B.left.Opens) (f : Γ(G.left, D.q.left ⁻¹ᵁ W)), UFib.HasWt D.i (D.q.left ⁻¹ᵁ W) f 0 → ∃ a : Γ(E.B.left, W), (D.q.left.app W).hom a = f := by
  intro k _ _ E G _ D W f hf
  have := D.q_affine
  refine (invariant_functions_descend _ G E.B _ D.q D.i D.q_hom D.i_hom D.q_flat D.q_surjective inferInstance
    D.isKernel W).2.2 f fun Z t g h₁ h₂ => fn_ext fun z _ => ?_
  rw [gs_id_appLE, gs_id_appLE, hf Z t g z (h₂ trivial), gm_charUnit_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
