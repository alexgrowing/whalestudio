import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AbDual

theorem exists_pow_eq_one_of_triv_ev_noeth : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ M : ℕ, 0 < M ∧ ∀ (T : Over (Sp B)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ M = 1 := by
  intro B _ _ A _ _ P hA hP h0l h0r hsym hamp
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP _
  obtain ⟨H, _, i, hi, hm, hf, hfl, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup B A hA _ hL hamp
  haveI : IsCommMonObj H := GlobalTheory.AbelianImage.isCommMonObj_of_mono i
  obtain ⟨M, hM, h1⟩ := GlobalTheory.FiniteFlatKilled.main B H hf hfl
  refine ⟨M, hM, fun T x hx => ?_⟩
  obtain ⟨z, rfl⟩ := (hH T x).1 (memKL_diag_of_triv_ev_of_symm B A hA P hP h0l h0r hsym T x hx)
  have h2 : z ^ M = 1 := by
    rw [← Category.comp_id z, ← MonObj.comp_pow, h1, MonObj.comp_one]
  rw [← MonObj.pow_comp, h2, MonObj.one_comp]

end GlobalTheory.AbDual
