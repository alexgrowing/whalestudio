import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem antisymm_rename_sigmaCongrRight : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))),
    rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  intro ι _ m Q w
  classical
  unfold antisymm
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun v => ?_)
  rw [map_zsmul, rename_rename, smul_smul]
  have hf : (⇑(Equiv.sigmaCongrRight w) ∘ fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) =
      fun x : Root m => (⟨x.1, (Equiv.mulLeft w v) x.1 x.2⟩ : Root m) := by
    funext x; rfl
  rw [hf]
  congr 1
  have hs : (∏ τ, Equiv.Perm.sign ((Equiv.mulLeft w v) τ) : ℤˣ) =
      (∏ τ, Equiv.Perm.sign (w τ)) * ∏ τ, Equiv.Perm.sign (v τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Equiv.Perm.sign_mul]
  rw [hs, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]

end GlobalTheory.GoodMetric
