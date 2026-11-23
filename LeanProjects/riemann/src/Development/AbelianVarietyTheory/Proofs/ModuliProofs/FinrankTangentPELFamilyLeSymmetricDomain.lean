import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfLineSubsetDiscrete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentInjectsSymmetricAntilinearCommutingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmAntilinearCommCMLeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankEigenspaceOfLieMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTan

theorem finrank_derivation_le : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  intro l1 l2 _ hu E _ _ _ H D g J _ a w w' bas _ _ _ _ _ N' o _ b ρ R _ _ _ _ _ t τ hρ hP _ hun
  obtain ⟨t₀, m, u, Hm, χ, κ, hG, ⟨hm, -⟩, hκ, hD⟩ := GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting l1 l2 hu o g (N' ^ 2) J b R t hun
  have hx : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨act, act₀, hc, hdet⟩ := GlobalTheory.FibreAct.exists_fibre_act E H D g (N' ^ 2) J a bas o b ρ _ _ t τ _
    (algebraMap o ℂ) t₀.A m hP hx hm
  obtain ⟨F, hF⟩ := (GlobalTheory.KS.exists_linear_lift_action t₀.pol u Hm χ hG).2 (𝓞 E) act₀
  have hle := GlobalTheory.T.finrank_symm_antilinear_comm_CM_le E H t₀.pol.g D.p D.q (algebraMap o ℂ ρ) Hm F (LinearMap.range κ)
    (by rw [← map_pow, hρ]; simp) hG.ah.1 hG.ah.2.1
    (fun σ => by
      split_ifs with h
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).1 h)
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).2 h))
    (by
      rintro _ ⟨d, rfl⟩
      exact ⟨(hD d).1, fun c => (hD d).2 (act.act c) (act₀.act c) (F c) (hc c) (hF c)⟩)
  rw [LinearMap.finrank_range_of_inj hκ] at hle
  exact hle

end GlobalTheory.PelTan
