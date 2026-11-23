import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodTStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem fund_phiB_alg (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

theorem fund_zB (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zB l z = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) :=
  (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (GlobalTheory.RingIface.aB_eq_alg l _)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fundamental_exact (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l)
    (hφ : Per.φB l b = b) (hF : C.ι b ∈ Per.FilD l 0) :
    ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨-, hinj, -, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := GlobalTheory.T.bdR_filtration_laws l
  have hj := GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris
  obtain ⟨htu, ht1, -, hlu⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have htφ := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  obtain ⟨-, -, huz, -, -, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hA : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
    intro y y' h
    apply hj
    apply hinj
    rw [← C.ι_j, ← C.ι_j, h]
  have e1 : phiA l x = (l : Per.Acris l) ^ r * x := by
    apply hA
    rw [← fund_phiB_alg, map_mul, map_pow, map_natCast, ← hx, map_mul, map_pow, hφ,
      fund_phiB_alg, htφ, map_mul, map_natCast, mul_pow]
    ring
  have ht1' : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ∈ Per.FilD l 1 :=
    (hP 1 _).2 ht1
  have htr : ∀ n : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ^ n ∈ Per.FilD l (n : ℤ) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      exact hmul _ _ _ _ ih ht1'
  have e2 : C.j x ∈ Per.FilP l r := by
    rw [← hP, ← C.ι_j, ← hx, map_mul, map_pow, C.ι_j]
    have := hmul _ _ _ _ hF (htr r)
    rwa [zero_add] at this
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C r x e1 e2
  have e3 : (l : Per.Bcris l) ^ k * b = Per.zB l z := by
    apply (htu.pow r).mul_right_cancel
    have := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hx, ← fund_zB, ← mul_assoc] at this
    exact this
  refine ⟨(z : ℚ_[l]) / (l : ℚ_[l]) ^ k, ?_⟩
  apply (hlu.pow k).mul_left_cancel
  rw [e3, ← huz]
  have hl : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have e4 : (z : ℚ_[l]) = (l : ℚ_[l]) ^ k * ((z : ℚ_[l]) / (l : ℚ_[l]) ^ k) := by
    field_simp
  conv_rhs => rw [e4]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.MemLoc
