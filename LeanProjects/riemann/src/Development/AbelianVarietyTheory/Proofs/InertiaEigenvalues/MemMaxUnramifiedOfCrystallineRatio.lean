import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.FracAlg

theorem ratio_adjoin {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D] [IsDomain D]
    (ι : B →+* D) (hι : Function.Injective ι) (o : Ω →+* D)
    (hk : ∀ c : k, ∃ b : B, ι b = o (algebraMap k Ω c)) (x : Ω)
    (hx : ∃ a b : B, b ≠ 0 ∧ ι a = o x * ι b) (y : Ω) (hy : y ∈ IntermediateField.adjoin k {x}) :
    ∃ a b : B, b ≠ 0 ∧ ι a = o y * ι b := by
  have hne : ∀ b : B, b ≠ 0 → ι b ≠ 0 := fun b hb h => hb (hι (by rw [h, map_zero]))
  have hmul : ∀ b b' : B, b ≠ 0 → b' ≠ 0 → b * b' ≠ 0 := fun b b' hb hb' h =>
    mul_ne_zero (hne b hb) (hne b' hb') (by rw [← map_mul, h, map_zero])
  have h1 : (1 : B) ≠ 0 := fun h => one_ne_zero (α := D) (by rw [← map_one ι, h, map_zero])
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hx
  | algebraMap c =>
    obtain ⟨b, hb⟩ := hk c
    exact ⟨b, 1, h1, by rw [hb, map_one, mul_one]⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * b' + a' * b, b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_add, map_mul, e, e']
    ring
  | inv z _ hz =>
    obtain ⟨a, b, hb, e⟩ := hz
    by_cases h0 : z = 0
    · exact ⟨0, 1, h1, by simp [h0]⟩
    · have ho : o z ≠ 0 := by simpa using h0
      refine ⟨b, a, fun h => mul_ne_zero ho (hne b hb) (by rw [← e, h, map_zero]), ?_⟩
      rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
  | mul z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * a', b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_mul, e, e']
    ring

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

open GlobalTheory.MemLoc in

theorem norm_of_ratio {l : ℕ} [Fact l.Prime] (C : Core l) (a b : Per.Bcris l) (x : Om l) (hb : b ≠ 0)
    (hx : x ≠ 0) (e : C.ι a = C.oD x * C.ι b) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨r, a', ha'⟩ := bcris_eq_acris_localization_periodT_alt l C a
  obtain ⟨s, b', hb'⟩ := bcris_eq_acris_localization_periodT_alt l C b
  have hu := (core_t_unit_fil l C).1
  have hA : algebraMap (Per.Acris l) (Per.Bcris l) (a' * C.t ^ s) =
      a * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← ha', pow_add, mul_assoc]
  have hB : algebraMap (Per.Acris l) (Per.Bcris l) (b' * C.t ^ r) =
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← hb', add_comm r s, pow_add, mul_assoc]
  refine GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l C (a' * C.t ^ s) (b' * C.t ^ r) x (fun h => hb ?_) hx ?_
  · rw [h, map_zero] at hB
    exact ((hu.pow _).mul_left_eq_zero).1 hB.symm
  · apply (BdRField.bdR_isField l).2.1
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← C.ι_j, ← C.ι_j, hA, hB, map_mul C.ι, map_mul C.ι, e,
      mul_assoc]
    rfl

end

theorem mem_Kur_of_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  intro l _ P AI T a b x hb e
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨hF, -, hinj, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  have : IsDomain P.R.BdR := hF.isDomain
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral _
  refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional hint⟩
    (fun y hy hy0 => ?_) (IntermediateField.mem_adjoin_simple_self ℚ_[l] x)
  obtain ⟨a', b', hb', e'⟩ := ratio_adjoin (k := ℚ_[l]) (P.ιB : P.R.B →+* P.R.BdR) hinj
    (algebraMap (Om l) P.R.BdR)
    (fun c => ⟨algebraMap ℚ_[l] P.R.B c,
      (P.ιB.commutes c).trans (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR c)⟩) x ⟨a, b, hb, e⟩ y hy
  refine norm_of_ratio C (T.eB a') (T.eB b') y (fun h => hb' (T.eB.injective (h.trans (map_zero _).symm))) hy0 ?_
  rw [← hC.ι, ← hC.ι, ← hC.o, ← map_mul]
  exact congrArg T.eD e'

end GlobalTheory.FracAlg
