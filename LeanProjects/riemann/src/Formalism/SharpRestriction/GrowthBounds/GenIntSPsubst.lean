import Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
import Formalism.LocalToGlobal.CharacterGerms.SubstSubst

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

section GenPieces

variable {V : VF C}

theorem gen_mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem gen_mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

def GenLow (V : VF C) (N : ℕ) (A : MvPowerSeries (Fin 2) C) : Prop :=
  ∀ μ : Fin 2 →₀ ℕ, μ 0 ≤ N → V.MM (MvPowerSeries.coeff μ A)

theorem GenLow.mul {N : ℕ} {A R : MvPowerSeries (Fin 2) C} (hA : GenLow V N A) (hR : IntS V R) :
    GenLow V N (A * R) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => V.MM x) (fun _ _ => gen_mm_add) gen_mm_zero ?_
  rintro ⟨a, b⟩ hab
  have hab' : a + b = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have ha0 : a 0 ≤ N := by
    have : a 0 + b 0 = μ 0 := by rw [← hab', Finsupp.add_apply]
    omega
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' (hR b) (hA a ha0)

theorem gen_pw {N : ℕ} (hN : 0 < N) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m f)) :
    PowerSeries.constantCoeff (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f) = 0 ∧
      ∀ m, V.Ge 0 (PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, _root_.PowerSeries.coeff_subst_X_pow (by omega)]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf.1]
  · rw [_root_.PowerSeries.coeff_subst_X_pow (by omega)]
    split_ifs
    · simpa using hf.2 _
    · exact VF.Ge.zero 0

theorem gen_mm_pw {N : ℕ} (hN : 0 < N) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : V.MM (PowerSeries.coeff 1 f)) (m : ℕ) (hm : m ≤ N) :
    V.MM (PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  rw [_root_.PowerSeries.coeff_subst_X_pow (by omega)]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have hk : k ≤ 1 := by
      by_contra h
      have : N * 2 ≤ N * k := Nat.mul_le_mul_left N (by omega)
      omega
    rw [Nat.mul_div_cancel_left k hN]
    interval_cases k
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, gen_mm_zero]
    · simpa using hf1
  · exact gen_mm_zero

theorem gen_low_inV {N : ℕ} (hN : 0 < N) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : V.MM (PowerSeries.coeff 1 f)) :
    GenLow V N (inV 0 (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ N) f)) := by
  intro μ hμ
  unfold inV
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact gen_mm_pw hN hf0 hf1 _ hμ
  · exact gen_mm_zero

theorem gen_intS_X {τ : Type} (x : τ) : IntS V (MvPowerSeries.X x : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem gen_intS_psubst {τ : Type} {a : MvPowerSeries τ C} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : IntS V a)
    {f : PowerSeries C} (hf : ∀ m, V.Ge 0 (PowerSeries.coeff m f)) : IntS V (PowerSeries.subst a f) :=
  IntS.subst (σ := Unit) (fun _ => ha0) (fun _ => ha) (intS_ps.2 hf)

theorem gen_cc_psubst {τ : Type} {a : MvPowerSeries τ C} (ha0 : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  VP.cc_subst (σ := Unit) (fun _ => ha0) hf

theorem gen_van_exp {τ : Type} {T : Set τ} {E : MvPowerSeries τ C} (hE : Van T E) : Van T (mvExp E - 1) := by
  intro ν hν
  have hk : ∀ k, k ≠ 0 → MvPowerSeries.coeff ν (E ^ k) = 0 := fun k hk => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ']
    exact (hE.mul_right _) ν hν
  have e : MvPowerSeries.coeff ν (mvExp E) =
      ∑ k ∈ Finset.range (ν.degree + 1), MvPowerSeries.coeff ν (E ^ k) / (k.factorial : C) := rfl
  rw [map_sub, e, Finset.sum_eq_single 0 (fun k _ h => by rw [hk k h, zero_div]) (by simp)]
  simp

end GenPieces

section GenChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def genS (κ : Type) : MvPowerSeries (κ ⊕ Unit) C := MvPowerSeries.X (Sum.inr ())

def genL (κ : Type) (f : PowerSeries C) : MvPowerSeries (κ ⊕ Unit) C := PowerSeries.subst (genS (C := C) κ) f

def genPhi (N : ℕ) (δ : κ → PowerSeries C) : κ ⊕ Unit → MvPowerSeries (Fin 2) C :=
  Sum.elim (fun i => inV 0 (pw N δ i)) fun _ => MvPowerSeries.X 1

theorem genS_cc : MvPowerSeries.constantCoeff (genS (C := C) κ) = 0 := by
  simp [genS]

theorem subst_genL {ρ : Type} {b : κ ⊕ Unit → MvPowerSeries ρ C} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : PowerSeries C) : MvPowerSeries.subst b (genL κ f) = PowerSeries.subst (b (Sum.inr ())) f := by
  show MvPowerSeries.subst b (MvPowerSeries.subst (fun _ : Unit => genS (C := C) κ) f) =
    MvPowerSeries.subst (fun _ : Unit => b (Sum.inr ())) f
  rw [VP.subst_subst (fun _ => genS_cc) hb]
  congr 1
  funext u
  exact VP.subst_X hb _

theorem genL_alongCv {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (f : MvPowerSeries κ C) : MvPowerSeries.subst (fun i => genL κ (γ i)) f = genL κ (alongCv γ f) := by
  show _ = MvPowerSeries.subst (fun _ : Unit => genS (C := C) κ) (MvPowerSeries.subst γ f)
  rw [VP.subst_subst hγ (fun _ => genS_cc)]
  rfl

theorem genL_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) :
    genL κ (∑ k ∈ s, f k) = ∑ k ∈ s, genL κ (f k) := by
  unfold genL
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero genS_cc), map_sum]

theorem hAt_subst (X : RawChart C d I κ) {τ ρ : Type} [Finite τ] {c b : κ → MvPowerSeries τ C}
    (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    {Φ : τ → MvPowerSeries ρ C} (hΦ : ∀ s, MvPowerSeries.constantCoeff (Φ s) = 0) :
    MvPowerSeries.subst Φ (hAt X c b) =
      hAt X (fun i => MvPowerSeries.subst Φ (c i)) (fun i => MvPowerSeries.subst Φ (b i)) := by
  have hP : ∀ q, MvPowerSeries.constantCoeff (pairSubst c b q) = 0 := by
    intro q
    unfold pairSubst
    split_ifs
    · exact hc _
    · exact hb _
  unfold hAt
  rw [VP.subst_subst hP hΦ]
  congr 1
  funext q
  unfold pairSubst
  split_ifs <;> rfl

theorem gen_van_X (i : κ) :
    Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (κ ⊕ Unit) C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X, if_neg]
  rintro rfl
  exact hν (Sum.inl i) (by simp) ⟨i, rfl⟩

theorem gen_van_hAt (X : RawChart C d I κ)
    (h0 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    {b : κ → MvPowerSeries (κ ⊕ Unit) C} (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) (hAt X (fun i => MvPowerSeries.X (Sum.inl i)) b) := by
  unfold hAt
  refine Van.subst {q : Fin 2 × κ | q.1 = 0} ?_ ?_ ?_
  · intro q
    unfold pairSubst
    split_ifs
    · simp
    · exact hb _
  · intro q hq
    unfold pairSubst
    rw [if_pos (show q.1 = 0 from hq)]
    exact gen_van_X _
  · intro e he
    exact h0 e fun s hs => he s hs

end GenChart

end SelfConjCharts

open SelfConjCharts in
theorem generic_point_unit_congruence : GenericPointUnitCongruence := by
  intro C _ _ V d I _ κ _ X hB hBi ζ hζ n hn z ε δ hz hε hδ hNR hδ1 N hN0 p q hp
  have hζint : V.Ge 0 ζ := V.ge_of_pow_eq_one V.l_prime.ne_zero hζ
  have hzk : ∀ (k : ℕ) (i : κ), PowerSeries.constantCoeff (PowerSeries.rescale (ζ ^ k) (z i)) = 0 ∧
      ∀ m, V.Ge 0 (PowerSeries.coeff m (PowerSeries.rescale (ζ ^ k) (z i))) := by
    intro k i
    refine ⟨?_, fun m => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hz i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact ((hζint.pow k).pow m).mul_int ((hz i).2 m)
  have hεn : ∀ i, PowerSeries.constantCoeff (pw n ε i) = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m (pw n ε i)) :=
    fun i => gen_pw hn (hε i)
  have hδN : ∀ i, PowerSeries.constantCoeff (pw N δ i) = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m (pw N δ i)) :=
    fun i => gen_pw hN0 (hδ i)
  have hpt : ∀ f : PowerSeries C, (PowerSeries.constantCoeff f = 0 ∧ ∀ m, V.Ge 0 (PowerSeries.coeff m f)) →
      MvPowerSeries.constantCoeff (genL κ f) = 0 ∧ IntS V (genL κ f) := fun f hf =>
    ⟨gen_cc_psubst genS_cc hf.1, gen_intS_psubst genS_cc (gen_intS_X _) hf.2⟩

  have BI := (hBi (κ ⊕ Unit) V.l (fun k i => genL κ (PowerSeries.rescale (ζ ^ k) (z i)))
    (fun i => genL κ (pw n ε i)) (fun i => MvPowerSeries.X (Sum.inl i))
    (fun k i => hpt _ (hzk k i)) (fun i => hpt _ (hεn i)) (fun i => ⟨by simp, gen_intS_X _⟩) (by
      intro i
      have e1 : alongCv (pw n ε) (X.lg i) =
          PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv ε (X.lg i)) :=
        alongCv_repar (fun i => (hε i).1) (by simp [hn.ne']) _
      have e2 : ∀ k, PowerSeries.rescale (ζ ^ k) (alongCv z (X.lg i)) =
          alongCv (fun i => PowerSeries.rescale (ζ ^ k) (z i)) (X.lg i) := by
        intro k
        simp only [PowerSeries.rescale_eq_subst]
        exact (alongCv_repar (fun i => (hz i).1) (by simp) _).symm
      rw [genL_alongCv (fun i => (hεn i).1), e1, hNR i, genL_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [genL_alongCv (fun i => (hzk k i).1), e2 k])).2
  set E : MvPowerSeries (κ ⊕ Unit) C :=
    ∑ k ∈ Finset.range V.l, hAt X (fun i => MvPowerSeries.X (Sum.inl i))
        (fun i => genL κ (PowerSeries.rescale (ζ ^ k) (z i))) -
      hAt X (fun i => MvPowerSeries.X (Sum.inl i)) (fun i => genL κ (pw n ε i)) with hEdef
  have hEV : Van (Set.range (Sum.inl : κ → κ ⊕ Unit)) E := by
    intro ν hν
    rw [hEdef, map_sub, map_sum,
      Finset.sum_eq_zero fun k _ => gen_van_hAt X hB.axis0 (fun i => (hpt _ (hzk k i)).1) ν hν,
      gen_van_hAt X hB.axis0 (fun i => (hpt _ (hεn i)).1) ν hν, sub_zero]
  have hΦ0 : ∀ s, MvPowerSeries.constantCoeff (genPhi N δ s) = 0 := by
    intro s
    cases s with
    | inl i => exact gen_cc_psubst (by simp) (hδN i).1
    | inr u => simp [genPhi]
  have hΦint : ∀ s, IntS V (genPhi N δ s) := by
    intro s
    cases s with
    | inl i => exact gen_intS_psubst (by simp) (gen_intS_X _) (hδN i).2
    | inr u => exact gen_intS_X _
  have hXc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (κ ⊕ Unit) C) = 0 :=
    fun i => by simp
  have hsE : MvPowerSeries.subst (genPhi N δ) E =
      ∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε) := by
    rw [hEdef, ← MvPowerSeries.substAlgHom_apply (VP.hs hΦ0), map_sub, map_sum]
    simp only [MvPowerSeries.substAlgHom_apply]
    rw [hAt_subst X hXc (fun i => (hpt _ (hεn i)).1) hΦ0]
    refine congrArg₂ _ (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [hAt_subst X hXc (fun i => (hpt _ (hzk k i)).1) hΦ0]
      simp only [VP.subst_X hΦ0, subst_genL hΦ0]
      rfl
    · simp only [VP.subst_X hΦ0, subst_genL hΦ0]
      rfl
  have hG : mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1 =
      MvPowerSeries.subst (genPhi N δ) (mvExp E - 1) := by
    rw [← MvPowerSeries.substAlgHom_apply (VP.hs hΦ0), map_sub, map_one, MvPowerSeries.substAlgHom_apply,
      VP.subst_exp hΦ0 hEV.const, hsE]
  have hF : IntS V (mvExp E - 1) := fun μ => by
    rw [map_sub]
    exact (BI μ).sub (IntS.one μ)
  have hFV := gen_van_exp hEV
  rw [hG, MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hΦ0)]
  refine finsum_induction (fun x => V.MM x) gen_mm_zero (fun _ _ => gen_mm_add) fun e => ?_
  rw [smul_eq_mul]
  by_cases h : ∀ s ∈ e.support, s ∉ Set.range (Sum.inl : κ → κ ⊕ Unit)
  · rw [hFV e h, zero_mul]
    exact gen_mm_zero
  · push Not at h
    obtain ⟨s0, hs0, i0, rfl⟩ := h
    have hp' : GenLow V N (e.prod fun s m => genPhi N δ s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs0]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs0)
      dsimp only
      rw [hm, Nat.succ_eq_add_one, pow_succ', mul_assoc]
      exact (gen_low_inV hN0 (hδ i0).1 (hδ1 i0)).mul ((IntS.pow (hΦint _) m).mul
        (Finset.prod_induction _ (IntS V) (fun _ _ h1 h2 => h1.mul h2) IntS.one fun s _ => (hΦint s).pow _))
    exact MaximalIdealCongruence.mm_mul_ge' (hF e) (hp' _ (by simpa [ee] using hp))

end Formalism.L2.FormalSeriesBounds
