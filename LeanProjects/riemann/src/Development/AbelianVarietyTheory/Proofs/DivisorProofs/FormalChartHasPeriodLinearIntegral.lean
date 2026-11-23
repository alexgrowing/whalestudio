import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

open MvPowerSeries in

theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add, ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
