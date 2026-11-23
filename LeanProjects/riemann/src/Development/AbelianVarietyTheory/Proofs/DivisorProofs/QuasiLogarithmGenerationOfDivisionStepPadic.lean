import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.Conv

section SlopeTestRemainingChoices

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem exists_lim {p : ℕ} (h : IsFrame p E (RingHom.id O)) (a : ℕ → O) :
    ∃ L : O, ∀ N : ℕ, ∃ c : O,
      L = ∑ n ∈ Finset.range N, (p : O) ^ n * a n + (p : O) ^ N * c := by
  obtain ⟨L, hL⟩ := h.complete.toIsPrecomplete.prec
    (f := fun N => ∑ n ∈ Finset.range N, (p : O) ^ n * a n) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left]
      exact dvd_neg.2 (Finset.dvd_sum fun k hk => dvd_mul_of_dvd_left
        (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _))
  refine ⟨L, fun N => ?_⟩
  have hN : (∑ n ∈ Finset.range N, (p : O) ^ n * a n) ≡ L
      [SMOD (Ideal.span {(p : O)}) ^ N • (⊤ : Submodule O O)] := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨-c, by linear_combination -hc⟩

theorem eq_zero_of_forall {p : ℕ} (h : IsFrame p E (RingHom.id O)) {x : E}
    (hx : ∀ N : ℕ, ∃ b : O, x = algebraMap O E ((p : O) ^ N * b)) : x = 0 := by
  obtain ⟨b, hb⟩ := hx 0
  have h0 : (p : O) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun N => by
    obtain ⟨c, hc⟩ := hx N
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [hb, h0, map_zero]

theorem comb_add_mul {ι : Type} [Fintype ι] (x y : ι → O) (c : O)
    (e : ι → MvPowerSeries (Fin d) E) :
    comb (fun i => x i + c * y i) e = comb x e + algebraMap O E c • comb y e := by
  unfold comb
  simp only [map_add, map_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

def IntD (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (g : MvPowerSeries (Fin d) E) : Prop :=
  (∀ i, ∃ b : O, lin g i = algebraMap O E b) ∧ In (⊤ : Ideal O) (cob1 (up E μ) g)

variable {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}

theorem up_const (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp [up, hμ]

theorem IntD.ofQL {g : MvPowerSeries (Fin d) E} (hg : QL μ ⊤ g) : IntD μ g :=
  ⟨fun i => (hg.2.1 i).imp fun _ hb => hb.2, hg.2.2⟩

theorem IntD.zero (hμ : ∀ i, constantCoeff (μ i) = 0) : IntD μ (0 : MvPowerSeries (Fin d) E) := by
  have h0 : cob1 (up E μ) (0 : MvPowerSeries (Fin d) E) = 0 := by
    simpa using formalCoboundary_smul (up_const hμ) (0 : E) (0 : MvPowerSeries (Fin d) E)
  refine ⟨fun i => ⟨0, by simp [lin]⟩, fun α => ⟨0, trivial, by simp [h0]⟩⟩

theorem IntD.add (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g + g') := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    obtain ⟨b', hb'⟩ := hg'.1 i
    refine ⟨b + b', ?_⟩
    simp only [lin, map_add] at hb hb' ⊢
    rw [hb, hb']
  · obtain ⟨b, -, hb⟩ := hg.2 α
    obtain ⟨b', -, hb'⟩ := hg'.2 α
    exact ⟨b + b', trivial, by rw [formalCoboundary_add (up_const hμ), map_add, hb, hb', map_add]⟩

theorem IntD.smul (hμ : ∀ i, constantCoeff (μ i) = 0) (c : O) {g : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) : IntD μ (algebraMap O E c • g) := by
  refine ⟨fun i => ?_, fun α => ?_⟩
  · obtain ⟨b, hb⟩ := hg.1 i
    refine ⟨c * b, ?_⟩
    simp only [lin, coeff_smul] at hb ⊢
    rw [hb, map_mul]
  · obtain ⟨b, -, hb⟩ := hg.2 α
    exact ⟨c * b, trivial, by rw [formalCoboundary_smul (up_const hμ), coeff_smul, hb, map_mul]⟩

theorem IntD.sub (hμ : ∀ i, constantCoeff (μ i) = 0) {g g' : MvPowerSeries (Fin d) E}
    (hg : IntD μ g) (hg' : IntD μ g') : IntD μ (g - g') := by
  have : g - g' = g + algebraMap O E (-1) • g' := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact hg.add hμ (hg'.smul hμ _)

theorem IntD.comb (hμ : ∀ i, constantCoeff (μ i) = 0) {ι : Type} [Fintype ι] (b : ι → O)
    {e : ι → MvPowerSeries (Fin d) E} (he : ∀ i, IntD μ (e i)) : IntD μ (comb b e) :=
  Finset.sum_induction _ (IntD μ) (fun _ _ h1 h2 => h1.add hμ h2) (IntD.zero hμ)
    fun i _ => (he i).smul hμ (b i)

theorem IntD.map (hμ : ∀ i, constantCoeff (μ i) = 0) (s : MvPowerSeries (Fin d) O) :
    IntD μ (MvPowerSeries.map (algebraMap O E) s) := by
  refine ⟨fun i => ⟨coeff (Finsupp.single i 1) s, by simp [lin, coeff_map]⟩, ?_⟩
  have := ((map_cob_swap_pull O d μ hμ E (algebraMap O E)).1 s).symm
  rw [show cob1 (up E μ) (MvPowerSeries.map (algebraMap O E) s) =
      MvPowerSeries.map (algebraMap O E) (cob1 μ s) from this]
  exact In.top_iff.2 ⟨_, rfl⟩

end SlopeTestRemainingChoices

theorem generate_of_step : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  intro p _ O E _ _ _ h d μ hμ ι _ e he H f hf
  have hc := hμ.const
  choose! bf sf ff hQ hff using H
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → MvPowerSeries (Fin d) E, F 0 = f ∧ ∀ n, F (n + 1) = ff (F n) :=
    ⟨fun n => ff^[n] f, rfl, fun n => Function.iterate_succ_apply' ff n f⟩
  have hFQ : ∀ n, QL μ ⊤ (F n) := by
    intro n
    induction n with
    | zero => rw [hF0]; exact hf
    | succ n ih => rw [hFs]; exact hQ _ ih
  have step : ∀ n, F n = comb (bf (F n)) e + map (algebraMap O E) (sf (F n)) + (p : E) • F (n + 1) :=
    fun n => by rw [hFs]; exact hff _ (hFQ n)
  have hpE : ∀ N : ℕ, (p : E) ^ N = algebraMap O E ((p : O) ^ N) := fun N => by
    rw [map_pow, map_natCast]
  have tele : ∀ N : ℕ, f = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
      ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) + (p : E) ^ N • F N := by
    intro N
    induction N with
    | zero =>
      have : comb (fun _ : ι => (0 : O)) e = 0 := by simp [comb]
      simp only [Finset.range_zero, Finset.sum_empty, this, pow_zero, one_smul, zero_add, hF0]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [comb_add_mul, ← hpE]
      have hs := step N
      rw [ih] at *
      linear_combination (norm := module) ((p : E) ^ N) • hs
  choose Bv hB using fun i => exists_lim h (fun n => bf (F n) i)
  choose Sc hS using fun α => exists_lim h (fun n => coeff α (sf (F n)))
  obtain ⟨S, hSd⟩ : ∃ S : MvPowerSeries (Fin d) O, ∀ α, coeff α S = Sc α := ⟨Sc, fun _ => rfl⟩
  have key : ∀ N : ℕ, ∃ g, Conv.IntD μ g ∧
      f - comb Bv e - map (algebraMap O E) S = (p : E) ^ N • g := by
    intro N
    choose cB hcB using fun i => hB i N
    choose cS hcS using fun α => hS α N
    obtain ⟨T, hTd⟩ : ∃ T : MvPowerSeries (Fin d) O, ∀ α, coeff α T = cS α := ⟨cS, fun _ => rfl⟩
    refine ⟨F N - comb cB e - map (algebraMap O E) T, ?_, ?_⟩
    · exact ((IntD.ofQL (hFQ N)).sub hc (IntD.comb hc cB fun i => IntD.ofQL (he i))).sub hc
        (IntD.map hc T)
    · have h1 : comb Bv e = comb (fun i => ∑ n ∈ Finset.range N, (p : O) ^ n * bf (F n) i) e +
          (p : E) ^ N • comb cB e := by
        rw [hpE, ← comb_add_mul]
        congr 1
        funext i
        exact hcB i
      have h2 : map (algebraMap O E) S =
          ∑ n ∈ Finset.range N, (p : E) ^ n • map (algebraMap O E) (sf (F n)) +
            (p : E) ^ N • map (algebraMap O E) T := by
        ext α
        rw [coeff_map, hSd, hcS α, map_add, map_add, coeff_smul, coeff_map, hTd, map_sum (coeff α)]
        simp only [coeff_smul, coeff_map, map_sum, map_mul, map_pow, map_natCast]
      rw [h1, h2]
      linear_combination (norm := module) tele N
  have hR : f - comb Bv e - map (algebraMap O E) S = 0 := by
    refine GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E h d μ hμ _ ?_ ?_
    · funext i
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, hb⟩ := hg.1 i
      refine ⟨b, ?_⟩
      rw [hgN]
      simp only [lin, coeff_smul] at hb ⊢
      rw [hb, hpE, map_mul]
    · ext α
      rw [coeff_zero]
      refine Conv.eq_zero_of_forall h fun N => ?_
      obtain ⟨g, hg, hgN⟩ := key N
      obtain ⟨b, -, hb⟩ := hg.2 α
      refine ⟨b, ?_⟩
      rw [hgN, formalCoboundary_smul (up_const hc), coeff_smul, hb, hpE, map_mul]
  exact ⟨Bv, In.top_iff.2 ⟨S, (sub_eq_zero.1 hR).symm⟩⟩

end GlobalTheory.QLog.Conv
