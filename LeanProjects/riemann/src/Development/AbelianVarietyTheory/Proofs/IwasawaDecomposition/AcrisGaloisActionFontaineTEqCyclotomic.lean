import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdRStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.TAct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

variable {l : ℕ} [Fact l.Prime]

theorem logA_mul {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e e' : Per.Fl l} {y y' : Per.Acris l}
    (he : e.untilt = 1) (he' : e'.untilt = 1) (hy : IsLogA e y) (hy' : IsLogA e' y') :
    IsLogA (e * e') (y + y') := by
  have hee : (e * e').untilt = 1 := by rw [map_mul, he, he', one_mul]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e * e') hee
  have h := GlobalTheory.MemLoc.LogAdd.log_add l e e' (j y) (j y') (j z) he he'
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e y he hy).2.2.2 j hj) ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e' y' he' hy').2.2.2 j hj)
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ z hee hz).2.2.2 j hj)
  rw [← map_add] at h
  rw [← GlobalTheory.T.acrisToBdRPlus_injective l j hj h]
  exact hz

theorem logA_pow {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) {e : Per.Fl l} {y : Per.Acris l}
    (he : e.untilt = 1) (hy : IsLogA e y) (n : ℕ) : IsLogA (e ^ n) ((n : Per.Acris l) * y) := by
  induction n with
  | zero =>
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l 1 h1
    have h2 := logA_mul hj h1 h1 hz hz
    rw [one_mul] at h2
    have h3 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l 1 z h1 hz).1 _ h2
    have h4 : z = 0 := by simpa using h3
    rw [pow_zero, Nat.cast_zero, zero_mul, ← h4]
    exact hz
  | succ n ih =>
    have := logA_mul hj (by rw [map_pow, he, one_pow]) he ih hy
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact this

theorem iter_pow (e : Per.Fl l) (m : ℕ) :
    (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e) ^ (l ^ m) = e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have : ∀ x : Per.Fl l, ((frobeniusEquiv (Per.Fl l) l).symm x) ^ l = x := fun x => by
      rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    rw [this, ih]

theorem eps_untilt (C : Core l) : C.ε.untilt = 1 := by
  have h := C.ε_root 0
  rw [C.ζ_zero, map_one] at h
  exact Subtype.ext h

theorem zeta_pow (C : Core l) (m : ℕ) : C.ζ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [C.ζ_zero]
  | succ m ih => rw [pow_succ', pow_mul, C.ζ_succ, ih]

theorem cong (C : Core l) (g : GQ l) (m : ℕ) : ∃ w : Per.Acris l,
    sigA g C.t - ((PadicInt.toZModPow m (C.χ g : ℤ_[l])).val : Per.Acris l) * C.t = (l : Per.Acris l) ^ m * w := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set a := (PadicInt.toZModPow m (C.χ g : ℤ_[l])).val with ha
  obtain ⟨b, hb⟩ : ∃ b, a + b = l ^ m := Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm
  set em := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] C.ε with hem
  have hε := eps_untilt C
  have hr : ((em.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m) := C.ε_root m
  have he : (Per.σF g em * em ^ b).untilt = 1 := by
    rw [map_mul, map_pow, GlobalTheory.RingBasics.untilt_σF]
    apply Subtype.ext
    have h1 : ((Per.σO g em.untilt : Per.OC l) : ℂ_[l]) = Per.σC g (em.untilt : ℂ_[l]) :=
      GlobalTheory.RingIface.sigO_coe l g _
    have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (C.ζ m)) = algebraMap (Om l) ℂ_[l] (g (C.ζ m)) :=
      GlobalTheory.RingBasics.σC_coe g _
    push_cast
    rw [h1, hr, h2, C.χ_cyc g m _ (zeta_pow C m), ← ha, ← map_pow, ← map_mul, ← pow_add, hb, zeta_pow, map_one]
  obtain ⟨z, _, hz, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l _ he
  have h1 := logA_pow C.j_cris he hz (l ^ m)
  have hgε : (Per.σF g C.ε).untilt = 1 := by rw [GlobalTheory.RingBasics.untilt_σF, hε, map_one]
  have h2 := logA_mul C.j_cris hgε (by rw [map_pow, hε, one_pow])
    ((GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ hε C.t_log).2.1 g) (logA_pow C.j_cris hε C.t_log b)
  have h3 : (Per.σF g em * em ^ b) ^ (l ^ m) = Per.σF g C.ε * C.ε ^ b := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm b, pow_mul, hem, iter_pow]
  rw [h3] at h1
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l _ _ (by rw [map_mul, hgε, map_pow, hε, one_pow, one_mul]) h1).1 _ h2
  refine ⟨z - C.t, ?_⟩
  have h5 : (a : Per.Acris l) + b = (l : Per.Acris l) ^ m := by exact_mod_cast congrArg (Nat.cast : ℕ → Per.Acris l) hb
  push_cast at h4
  linear_combination h4 - C.t * h5

theorem t_act : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l),
    sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  intro l _ C g
  haveI := (acris_basic l).1
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Per.Acris l)})]
  intro m
  obtain ⟨w, hw⟩ := cong C g m
  set x : ℤ_[l] := (C.χ g : ℤ_[l])
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) hc
  rw [map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply] at hc'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨w - algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t, ?_⟩
  linear_combination - hw - C.t * hc'

end GlobalTheory.MemLoc.TAct
