import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobXiDivPrimeUnitTendstoOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegreeStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.LTPeriod

variable {l : ℕ} [Fact l.Prime]

theorem iter_φB_alg (k : ℕ) (y : Per.Acris l) :
    (⇑(Per.φB l))^[k] (algebraMap (Per.Acris l) (Per.Bcris l) y) =
      algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(GlobalTheory.MemLoc.phiA l))^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GlobalTheory.MemLoc.fund_phiB_alg, ih]

theorem phiA_alg (a : Per.Ainf l) :
    GlobalTheory.MemLoc.phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem iter_phiA_alg (k : ℕ) (a : Per.Ainf l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[k] (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[k] a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, phiA_alg, ih]

theorem iter_mul {A : Type} [CommRing A] (f : A →+* A) (k : ℕ) (a b : A) :
    (⇑f)^[k] (a * b) = (⇑f)^[k] a * (⇑f)^[k] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem iter_natCast {A : Type} [CommRing A] (f : A →+* A) (k m : ℕ) :
    (⇑f)^[k] (m : A) = m := by
  rw [← RingHom.coe_pow, map_natCast]

theorem concrete (C : GlobalTheory.MemLoc.Core l) (n : ℕ) (hn : 0 < n) :
    ∃ x : Per.Bcris l, IsUnit x ∧ (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x ∧ C.ι x ∈ Per.FilD l 1 ∧
      C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 ∧ C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul l C.ε he (m + 1) hn
  obtain ⟨u, hu, hlu, hconv⟩ := GlobalTheory.T.frobXi_div_prime_unit_tendsto_one l C
  obtain ⟨c, hc, hcφ⟩ :=
    GlobalTheory.T.exists_unit_frobenius_iterate_product_eq (Per.Acris l) l (GlobalTheory.MemLoc.acris_basic l).1 (GlobalTheory.MemLoc.phiA l) u hu hconv (m + 1) hn
  rw [Nat.add_sub_cancel] at hcφ
  set ξ := GlobalTheory.MemLoc.xi C.ε with hξ
  have h1 : (l : Per.Acris l) * (⇑(GlobalTheory.MemLoc.phiA l))^[m] u =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) := by
    rw [← iter_natCast (GlobalTheory.MemLoc.phiA l) m l, ← iter_mul, hlu, iter_phiA_alg,
      ← Function.iterate_succ_apply]
  have hkey : algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) *
      (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] c = (l : Per.Acris l) * c := by
    rw [← h1]
    linear_combination (l : Per.Acris l) * hcφ
  set a : Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w) * c with ha
  have hA : (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] a = (l : Per.Acris l) * a := by
    rw [ha, iter_mul, iter_phiA_alg, iter_mul, hw, map_mul, map_mul]
    linear_combination (algebraMap (Per.Ainf l) (Per.Acris l) ξ *
      algebraMap (Per.Ainf l) (Per.Acris l) w) * hkey
  set x : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) a with hx
  have hxφ : (⇑(Per.φB l))^[m + 1] x = (l : Per.Bcris l) * x := by
    rw [hx, iter_φB_alg, hA, map_mul, map_natCast]
  have hxa : x = Per.aB l (ξ * w) * algebraMap (Per.Acris l) (Per.Bcris l) c := by
    have e : algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w)) =
        Per.aB l (ξ * w) := by
      apply (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.1
      rw [GlobalTheory.MemLoc.PrimeEx.iota_aB, C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris]
    rw [hx, ha, map_mul, e]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hxa, (hc.map (algebraMap (Per.Acris l) (Per.Bcris l))).mul_left_eq_zero] at h0
    exact hw0 (GlobalTheory.MemLoc.PrimeEx.aB_inj C (h0.trans (map_zero _).symm))
  have hx1 : C.ι x ∈ Per.FilD l 1 := by
    rw [hxa, map_mul, C.ι_j, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ((GlobalTheory.MemLoc.PrimeEx.fil1 C _).2 ⟨w, rfl⟩)
  have hx0' : ∀ j : ℕ, j < m + 1 → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 := by
    intro j _
    rw [hx, iter_φB_alg, C.ι_j]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _
  obtain ⟨hunit, h2, hj⟩ := GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree l C (m + 1) hn x hxφ hx0 hx1 hx0'
  exact ⟨x, hunit, hxφ, hx1, h2, fun j hj0 hjn => ⟨hx0' j hjn, hj j hj0 hjn⟩⟩

end GlobalTheory.LTPeriod

theorem GlobalTheory.LTPeriod.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧
      P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K n hn
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.concrete C n hn
  have hit : ∀ (k : ℕ) (b : P.R.B), T.eB ((⇑P.φB)^[k] b) = (⇑(Per.φB l))^[k] (T.eB b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hfil : ∀ (a : ℤ) (b : P.R.B), P.ιB b ∈ (P.PD K).Fil a ↔ C.ι (T.eB b) ∈ Per.FilD l a := by
    intro a b
    rw [T.fil, hC.ι]
  refine ⟨T.eB.symm x, hu.map T.eB.symm, T.eB.injective ?_, ?_, ?_, fun j hj0 hjn => ?_⟩
  · rw [hit, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h1
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h2
  · rw [hfil, hfil, hit, RingEquiv.apply_symm_apply]
    exact hj j hj0 hjn
