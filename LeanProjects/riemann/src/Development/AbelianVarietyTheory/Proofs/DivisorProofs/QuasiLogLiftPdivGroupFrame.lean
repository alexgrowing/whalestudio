import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_add {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  obtain ⟨b, hb, e'⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, e, e', map_add]⟩

theorem in_mono {σ : Type} {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' f := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨a, h ha, e⟩

theorem in_map {σ : Type} (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b))
    {N N' : Ideal B} (hN : ∀ b ∈ N, t b ∈ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' (map s f) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨t a, hN a ha, by rw [coeff_map, e, hs]⟩

theorem in_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) {N : Ideal B} {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (expand p hp f) := fun α => by
  by_cases h : ∀ i, p ∣ α i
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, p • m = α := ⟨α.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [← hm, coeff_expand_smul]
    exact hf m
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨0, N.zero_mem, by rw [coeff_expand_of_not_dvd p hp f hi, map_zero]⟩

theorem frob_congr (p : ℕ) [Fact p.Prime] (t : B →+* B) (ht : ∀ b, (p : B) ∣ t b - b ^ p)
    (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_expand (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

theorem cob1_expand_frobenius_map (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    cob1 (up Q μ) (expand p hp (map s f)) =
      (subst (up Q fun i => μ i ^ p) (map s f) -
        subst (up Q fun i => expand p hp (map t (μ i))) (map s f)) +
        expand p hp (map s (cob1 (up Q μ) f)) := by
  have hU : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hexp : ∀ {σ : Type} (g : MvPowerSeries σ Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have hmapU : (fun i => map s (up Q μ i)) = up Q (fun i => map t (μ i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have e1 : subst (up Q μ) (expand p hp (map s f)) = subst (up Q fun i => μ i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have e2 : inL (expand p hp (map s f)) = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inL, hexp, subst_comp_subst_apply hXp hL]
    congr 1
    funext i
    rw [subst_pow hL, subst_X hL]
  have e3 : inR (expand p hp (map s f)) = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inR, hexp, subst_comp_subst_apply hXp hR]
    congr 1
    funext i
    rw [subst_pow hR, subst_X hR]
  have hV : HasSubst (up Q fun i => map t (μ i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have m1 : map s (subst (up Q μ) f) = subst (up Q fun i => map t (μ i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have m2 : map s (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hL]; congr 1; funext i; simp
  have m3 : map s (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hR]; congr 1; funext i; simp
  have x1 : expand p hp (subst (up Q fun i => map t (μ i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have x2 : expand p hp (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hL]; congr 1; funext i; simp
  have x3 : expand p hp (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hR]; congr 1; funext i; simp
  have e4 : expand p hp (map s (cob1 (up Q μ) f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) -
        subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) -
        subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    simp only [cob1, inL, inR, map_sub, m1, m2, m3, x1, x2, x3]
  rw [cob1, e1, e2, e3, e4]
  abel

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog

open GlobalTheory.QLog.FrobQL in

theorem ql_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' →
    (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f →
    QL μ' ⊤ (frob p F.s f) ∧
      (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) →
        QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε F G d c μ' hμ _ f hf
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hu : ¬IsUnit (p : F.B) := fun h =>
    (Fact.out : ¬IsUnit (p : O)) (by simpa using h.map F.θ)
  rw [frob_eq_expand p hp]
  have hc0 : constantCoeff (expand p hp (map F.s f)) = 0 := by
    rw [constantCoeff_expand, constantCoeff_map, hf.1, map_zero]
  have hlin : ∀ i, lin (expand p hp (map F.s f)) i = 0 := fun i => by
    unfold lin
    exact coeff_expand_of_not_dvd p hp _ (i := i) (by simpa using hpp.not_dvd_one)
  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * b ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e]; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨b, _, e⟩ := h α i
    exact ⟨F.σ b, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e, F.s_alg]⟩
  have hK := GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d ⊕ Fin d) ⊤ (map F.s f)
    (fun i => μ' i ^ p) (fun i => expand p hp (map F.σ (μ' i))) hD
    (fun i => by rw [map_pow, hμ.const i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero])
    (fun i α => frob_congr p F.σ F.σ_pow hu (μ' i) α)
  rw [Ideal.mul_top] at hK
  simp only [QL]
  rw [cob1_expand_frobenius_map p hp F.σ F.s F.s_alg μ' hμ.const f]
  refine ⟨⟨hc0, fun i => ⟨0, trivial, by rw [hlin, map_zero]⟩,
    in_add (in_mono le_top hK) (in_expand p hp (in_map F.σ F.s F.s_alg (N' := ⊤) (fun _ _ => Submodule.mem_top) hf.2.2))⟩,
    fun hker => ⟨hc0, fun i => ⟨0, Ideal.zero_mem _, by rw [hlin, map_zero]⟩,
      in_add hK (in_expand p hp (in_map F.σ F.s F.s_alg ?_ hker))⟩⟩
  intro b hb
  rw [RingHom.mem_ker] at hb
  obtain ⟨y, _, hy⟩ := F.frame.pd b hb
  obtain ⟨z, hz⟩ := F.σ_pow b
  rw [Ideal.mem_span_singleton]
  exact ⟨z + y, by rw [mul_add, ← hz, ← hy]; ring⟩

end GlobalTheory.QLog
