import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes GlobalTheory.LKGeo.MultScale
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.MultiplicativeUnitDivisibility

variable {p : ℕ} [Fact p.Prime]

private theorem exists_dvd_EFA (D : Datum p) (d : ℤ) (hd : ∀ x y : D.La, d ∣ D.EF x y)
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    ∃ c : AfP p, IsIntAf c ∧ EFA D v w = (d : AfP p) * c := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      obtain ⟨k, hk⟩ := hd x x'
      refine ⟨a * a' * (k : AfP p), isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast k), ?_⟩
      rw [EFA_tmul, hk]
      push_cast
      ring
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨c, hc, e⟩ := h
      obtain ⟨c', hc', e'⟩ := h'
      exact ⟨c + c', isIntAf_add hc hc', by rw [map_add, e, e', mul_add]⟩
    | neg u _ h =>
      obtain ⟨c, hc, e⟩ := h
      exact ⟨-c, isIntAf_neg hc, by rw [map_neg, e, mul_neg]⟩
  | zero => exact ⟨0, isIntAf_zero, by simp⟩
  | add u u' _ _ h h' =>
    obtain ⟨c, hc, e⟩ := h
    obtain ⟨c', hc', e'⟩ := h'
    exact ⟨c + c', isIntAf_add hc hc', by rw [map_add, LinearMap.add_apply, e, e', mul_add]⟩
  | neg u _ h =>
    obtain ⟨c, hc, e⟩ := h
    exact ⟨-c, isIntAf_neg hc, by rw [map_neg, LinearMap.neg_apply, e, mul_neg]⟩

private theorem exists_ne (D : Datum p) : ∃ x y : D.La, D.EF x y ≠ 0 := by
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hr : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  haveI := Module.nontrivial_of_finrank_pos hr
  obtain ⟨x, hx⟩ := _root_.exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := by
    intro h
    apply hx
    apply D.nondeg
    rw [h, map_zero]
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

private theorem isUnit_intCast {d : ℤ} (hd : d ≠ 0) : IsUnit (d : AfP p) := by
  have h : IsUnit (d : ℚ) := (Int.cast_ne_zero.mpr hd).isUnit
  simpa using h.map (algebraMap ℚ (AfP p))

private theorem isIntAf_sim {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf)
    (hg : ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D) : IsIntAf ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) := by
  let S : Set ℤ := {z | ∃ x y : D.La, D.EF x y = z}
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal (Ideal.span S)).principal
  have hdvd : ∀ x y : D.La, d ∣ D.EF x y := by
    intro x y
    have hm : D.EF x y ∈ Ideal.span S := Ideal.subset_span ⟨x, y, rfl⟩
    rw [hdI] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := exists_ne D
    apply hxy
    obtain ⟨k, hk⟩ := hdvd x y
    rw [hk, zero_mul]
  have key : ∀ z ∈ Ideal.span S, ∃ c : AfP p, IsIntAf c ∧
      ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * (z : AfP p) = (d : AfP p) * c := by
    intro z hz
    change z ∈ Submodule.span ℤ S at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      have h1 := EFA_actG L g (inAf D x) (inAf D y)
      rw [EFA_inAf] at h1
      rw [← h1]
      exact exists_dvd_EFA D d hdvd (hg _ (inAf_mem D x)) (hg _ (inAf_mem D y))
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add a b _ _ h1 h2 =>
      obtain ⟨c1, h1i, h1e⟩ := h1
      obtain ⟨c2, h2i, h2e⟩ := h2
      refine ⟨c1 + c2, isIntAf_add h1i h2i, ?_⟩
      rw [Int.cast_add, mul_add, h1e, h2e, mul_add]
    | smul a b _ h =>
      obtain ⟨c, hi, he⟩ := h
      refine ⟨a * c, isIntAf_mul (isIntAf_intCast a) hi, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨c, hc, hce⟩ := key d (by rw [hdI]; exact Submodule.mem_span_singleton_self d)
  have hsc : ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) = c :=
    (isUnit_intCast (p := p) hd0).mul_left_cancel (by rw [mul_comm]; exact hce)
  rw [hsc]
  exact hc

private theorem pow_dvd_of_isIntAf {q k c c' : ℕ} (hq : q.Prime) (hqp : q ≠ p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) (hd : q ^ k ∣ c') : q ^ k ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  have hm : IsIntAf ((m : AfP p) * t) := by
    have hmi := isIntAf_intCast (p := p) (m : ℤ)
    rw [Int.cast_natCast] at hmi
    exact isIntAf_mul hmi ht
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let v0 : HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime hq0).mpr hqz,
      by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0⟩
  have hv0p : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro heq
    have hmem : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := heq ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hmem
    have hpq : p ∣ q := Int.natCast_dvd_natCast.mp hmem
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpq).symm
  let v : AwayP p := ⟨v0, hv0p⟩
  have hev : (AfP.eval v) (c : AfP p) =
      (q : HeightOneSpectrum.adicCompletion ℚ v0) ^ k * (AfP.eval v) ((m : AfP p) * t) := by
    rw [h, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, map_natCast]
  have hval : ∀ n : ℕ, Valued.v (n : HeightOneSpectrum.adicCompletion ℚ v0) = v0.intValuation (n : ℤ) := by
    intro n
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v0 (n : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [← h1]
    congr 1
    simp
  have hs : Valued.v ((AfP.eval v) ((m : AfP p) * t)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v0).mp (hm v)
  have hle : v0.intValuation (c : ℤ) ≤ WithZero.exp (-(k : ℤ)) := by
    have hc := hval c
    rw [map_natCast] at hev
    rw [← hc, hev, map_mul, map_pow, hval q, HeightOneSpectrum.intValuation_singleton v0 hq0 rfl]
    refine (mul_le_of_le_one_right' hs).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hle
  change Ideal.span {(q : ℤ)} ^ k ∣ Ideal.span {(c : ℤ)} at hle
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at hle
  exact_mod_cast hle

private theorem dvd_of_isIntAf {c c' : ℕ} (hc' : c'.Coprime p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) : c' ∣ c := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd c c']
  intro q k hq hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hqp : q ≠ p := by
      rintro rfl
      have hqc : q ∣ c' := (dvd_pow_self q hk.ne').trans hqk
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqc hc') dvd_rfl)
    exact pow_dvd_of_isIntAf hq hqp ht h hqk

private theorem main : MultUnit := by
  intro p _ D G L
  refine ⟨?_, ?_⟩
  · intro u hu
    have hst : ∀ g ∈ L.KN 1, ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
      intro g hg v hv
      obtain ⟨w, hw, e⟩ := hg.1 v hv
      rw [e, one_smul]
      exact add_mem hv hw
    have h1 := isIntAf_sim L u (hst u hu)
    have h2 := isIntAf_sim L u⁻¹ (hst _ (inv_mem hu))
    refine ⟨((uSimR (AfP p) u⁻¹ : (AfP p)ˣ) : AfP p), h1, h2, ?_⟩
    have h3 : (uSimR (AfP p) u⁻¹ : (AfP p)ˣ) = ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ := rfl
    rw [h3]
    exact Units.mul_inv _
  · intro c c' t t' hc hc' ht ht' htt h
    refine Nat.dvd_antisymm ?_ (dvd_of_isIntAf hc' ht h)
    refine dvd_of_isIntAf hc ht' ?_
    rw [h, mul_assoc, htt, mul_one]

end UpperTheory.MultiplicativeUnitDivisibility

theorem UpperTheory.multiplier_is_unit : MultUnit := UpperTheory.MultiplicativeUnitDivisibility.main
