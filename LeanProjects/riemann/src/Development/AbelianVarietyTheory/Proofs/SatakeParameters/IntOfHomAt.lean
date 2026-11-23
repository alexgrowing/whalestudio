import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.GO.ChRoot GlobalTheory.TopStep

namespace GlobalTheory.ColPeriod.EntQ

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem val_of_pow {a : K} {k : ℕ} (hk : 0 < k) (h : w.valuation K (a ^ k) = 1) : w.valuation K a = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h

theorem val_nat {q : ℕ} (hq : (q : 𝓞 K) ∉ w.asIdeal) : w.valuation K (q : K) = 1 := by
  have := (w.valuation_eq_one_iff_notMem (K := K) (r := (q : 𝓞 K))).2 hq
  simpa using this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem val_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.unitV χ a) ≤ 1 ∧ w.valuation K (LocE.unitV χ a)⁻¹ ≤ 1 := by
  by_cases h : LocE.unitV χ a = 0
  · simp [h]
  · obtain ⟨k, hk, h1⟩ := unitV_root χ a h
    have := val_of_pow w hk (a := LocE.unitV χ a) (by rw [h1, map_one])
    simp [this]

theorem val_locChar (q : ℕ) {cq : K} (hc : w.valuation K cq = 1) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.locChar q cq χ a) ≤ 1 ∧ w.valuation K (LocE.locChar q cq χ a)⁻¹ ≤ 1 := by
  unfold LocE.locChar
  rw [mul_inv, map_mul, map_mul, map_inv₀ _ (cq ^ _), map_zpow₀, hc, one_zpow, inv_one, one_mul, one_mul]
  exact val_unitV w χ _

theorem val_om {a b : ℕ} {mu : E → K} (hmu : ∀ t, w.valuation K (mu t) ≤ 1 ∧ w.valuation K (mu t)⁻¹ ≤ 1) (v : E → ℤ)
    {sq : K} (hsq : w.valuation K sq = 1) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E))
    {Φ : Loc.SF E K a b} (hΦ : ∀ x, w.valuation K (Φ x) ≤ 1) (x) : w.valuation K (Loc.om mu v sq g₀ h Φ x) ≤ 1 := by
  unfold Loc.om
  simp only [map_mul, map_zpow₀, hsq, one_zpow, mul_one]
  exact mul_le_one' (mul_le_one' (hmu _).1 (hmu _).2) (hΦ _)

theorem val_PhiQ (q : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    w.valuation K (LocE.PhiQ q χ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ
  split_ifs
  · exact (val_unitV w χ _).1
  · simp

end Val

section Supp

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_fIdx {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : ∃ s, s < n + c ∧ LocE.fIdx k₀ c n s = l := by
  refine ⟨LocE.fPos k₀ c n l, ?_, ?_⟩
  · unfold LocE.fPos
    split_ifs <;> omega
  · unfold LocE.fIdx LocE.fPos
    split_ifs <;> omega

theorem int_of_PhiQ {q : ℕ} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    {x : HomE E (n' + c') (n + c)} (hx : LocE.PhiQ q χ k₀ r c' n' c n x ≠ 0) {v : Sp E (n' + c')}
    (hv : v ∈ stdAt E (n' + c') P) : x v ∈ stdAt E (n + c) P := by
  unfold LocE.PhiQ at hx
  split_ifs at hx with h
  · rw [mem_stdAt] at hv ⊢
    intro i
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (hv j).mul ?_
    obtain ⟨p, hp, e⟩ := exists_fIdx hk i.2
    obtain ⟨p', hp', e'⟩ := exists_fIdx hk' j.2
    have h1 := h.1 p p' hp hp'
    have h2 : Loc.eN E (n' + c') j.1 = Pi.single j 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    simpa [LocE.entB, e, e', LocE.scE, Loc.atN, h2] using h1
  · exact absurd rfl hx

theorem intAt_chArg {n' c' n c : ℕ} (a : E) (x : HomE E (n' + c') (n + c))
    (h : ∀ v ∈ stdAt E (n' + c') P, a • x v ∈ stdAt E (n + c) P) : IntAt P (a * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero

theorem int_of_homAt {a b : ℕ} {z : HomE E a b} (hz : z ∈ homAt {P} (stdLat E a) (stdLat E b)) (B : ℕ) (s : Fin a) (l : Fin b) :
    IntAt P (((qOf P : E) ^ B)⁻¹ * (((qOf P : E) ^ B) • z) (Pi.single s 1) l) := by
  have h := mem_stdAt.1 (hz P (Finset.mem_singleton_self P) _ (single_mem_stdAt s)) l
  have hq := qOf_ne_zero (P := P)
  rwa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]

end Supp

theorem k_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem entryAtQ (hV : VolumeAtQ) : EntryAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 hL P w hP hdeg hq hmu
  have hm := hL.hm
  have hqv := val_nat w hq
  have hsq : w.valuation X.K (cst.sq P) = 1 := val_of_pow w two_pos (by rw [hL.cst_ok.sq_sq, hqv])
  have hom : ∀ i, i < R.m → ∀ hal h x, w.valuation X.K (omPhi Ch sel mu cst i P hal h x) ≤ 1 := by
    intro i hi hal h x
    refine val_om w (fun t => val_locChar w _ (hmu i hi) _ t) _ hsq _ _ (fun y => ?_) x
    rw [PhiAt, if_neg hP]
    exact val_PhiQ w _ _ _ _ _ _ _ _ y
  refine ⟨fun i hi al be => ⟨fun x => ?_, fun x z hz => hL.xiInv i hi al be P x _ (int_of_homAt hz _)⟩,
    fun al y => ⟨fun x => hom m2 (by omega) _ _ _, fun x z hz => hL.psiInvX al P x _ y (int_of_homAt hz _)⟩⟩
  unfold XiAt E1at Loc.E1
  rw [map_mul, map_mul, map_pow, map_inv₀ _ (_ ^ cst.B), map_pow, hqv, one_pow, inv_one, one_pow, one_mul]
  refine mul_le_one' (hV X Pr R _ _ _ _ w hP hdeg hq) (Valuation.map_sum_le _ fun t _ => ?_)
  generalize Loc.xx1 x t = y
  by_cases h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y = 0
  · simp [h0]
  rw [map_mul]
  refine mul_le_one' (hom i (by omega) _ _ _) (le_of_eq ?_)
  have h1 := right_ne_zero_of_mul h0
  rw [PhiAt, if_neg hP] at h1
  have hb := hL.boundQ i al P hP
  have hb' := hL.boundQ (i + 1) be P hP
  have hD := hL.depthQ' P hP
  simp only [lamYat, hP, if_false, mem_lamY_zero] at hb hb'
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
    refine intAt_chArg _ y fun v hv => ?_
    have h2 := (hb' _ (int_of_PhiQ (k_le_N R _) (k_le_N R _) h1 (hb v hv).1)).2
    have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [h3] using h2
  have hint' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact intAt_neg ((intAt_pow (intAt_nat _) _).mul hint)
  exact val_of_pow w (pow_pos (qOf_pos _) _) (by rw [psi_root hL.cst_ok P _ hint', map_one])

end GlobalTheory.ColPeriod.EntQ
