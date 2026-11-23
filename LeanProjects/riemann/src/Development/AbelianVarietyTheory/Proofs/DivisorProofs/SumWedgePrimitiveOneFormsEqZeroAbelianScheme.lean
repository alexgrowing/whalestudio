import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

private lemma add_add_eq_add_imp {M : Type} [AddCommGroup M] (a b c d : M) (h : (a + b) + (c + d) = a + d) :
    c + b = 0 := by
  calc c + b = (a + b) + (c + d) - (a + d) := by abel
    _ = 0 := by rw [h, sub_self]

theorem wsum_eq_zero_of_mul : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (n : ℕ) (u v : Fin n → GlobForm A.hom), wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) = wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) + wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) → wsum (OAff A.hom) u v = 0 := by
  intro R _ A _ g hA hs n u v hw
  have hP : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  obtain ⟨hF, hC, hA2, hs2⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  obtain ⟨hF2, hC2, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hA2 hs2
  obtain ⟨-, hax, -⟩ := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  let U : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (snd A A) (u k))
  let V : Fin (n + n) → GlobForm (A ⊗ A).hom :=
    Fin.append (fun k ↦ pF (snd A A) (v k)) (fun k ↦ pF (fst A A) (v k))
  have hUV : wsum (OAff (A ⊗ A).hom) U V = 0 := by
    funext T
    have h1 := congrFun hw T
    simp only [wsum, hP, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib] at h1
    simp only [wsum, Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right]
    exact add_add_eq_add_imp _ _ _ _ h1
  have key := (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R _ (OAff (A ⊗ A).hom) hF2 hC2 (n + n) U V).mp hUV
  refine (GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff R _ (OAff A.hom) hF hC n u v).mpr ?_
  intro l l'
  have h2 := key (l ∘ₗ pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (l' ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  simp only [Fin.sum_univ_add, U, V, Fin.append_left, Fin.append_right, LinearMap.comp_apply,
    (hax _).1, (hax _).2.1, (hax _).2.2.2.1, (hax _).2.2.2.2.1, map_zero, mul_zero, zero_mul, sub_zero,
    zero_sub] at h2
  rw [← h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.AbCoh
