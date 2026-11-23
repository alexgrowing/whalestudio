import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageGenerationStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependentStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BasisLift

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]

theorem comb_add (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b + c) e = comb b e + comb c e := by
  simp [comb, map_add, add_smul, Finset.sum_add_distrib]

theorem comb_sub (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b - c) e = comb b e - comb c e := by
  simp [comb, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem comb_zero (e : ι → MvPowerSeries σ Q) : comb (0 : ι → B) e = 0 := by
  simp [comb]

theorem comb_mul (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => r * b i) e = algebraMap B Q r • comb b e := by
  simp [comb, map_mul, mul_smul, Finset.smul_sum]

theorem comb_mul_right (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => b i * r) e = algebraMap B Q r • comb b e := by
  simp only [mul_comm _ r]; exact comb_mul r b e

theorem coeff_comb (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ i, algebraMap B Q (b i) * coeff α (e i) := by
  simp only [comb, map_sum, coeff_smul]

end GlobalTheory.BasisLift

open GlobalTheory.BasisLift in

theorem GlobalTheory.basis_lift : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL C _ _ hC Θ hΘ ι _ e he hB hch
  obtain ⟨u, hu⟩ := hF.unit_p
  have hmapP : algebraMap B Q (p : B) = (p : Q) := map_natCast _ _
  have hconst : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hL.const i]
  have ql0 : ∀ N : Ideal B, QL μ N (0 : MvPowerSeries (Fin d) Q) := by
    intro N
    refine ⟨by simp, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
    have h0 := formalCoboundary_smul hconst (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simp only [zero_smul] at h0
    simp [h0]
  have hsm : ∀ n : ℕ, (Ideal.span {(p : B)} ^ n • ⊤ : Submodule B B) = Ideal.span {(p : B) ^ n} := by
    intro n; rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have key : ∀ t ∈ Ideal.span {(p : B)}, ∃ t' : B, (↑u⁻¹ : Q) * algebraMap B Q t = algebraMap B Q t' := by
    intro t ht
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    refine ⟨a, ?_⟩
    rw [map_mul, hmapP, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

  have chainE : ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N →
      ∀ f, QL μ ⊤ f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q),
        In (⊤ : Ideal B) s ∧ QL μ N (f - comb b e - s) := by
    intro N hN
    induction hN with
    | refl => intro f hf; exact ⟨0, 0, fun α => ⟨0, trivial, by simp⟩, by simpa [comb_zero] using hf⟩
    | tail _ hst ih =>
      intro f hf
      obtain ⟨b, s, hs, hq⟩ := ih f hf
      obtain ⟨b', s', -, hs', hq'⟩ := GlobalTheory.T.quasiLogarithm_devissage_generation_step p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst _ hq
      refine ⟨b + b', s + s', ?_, ?_⟩
      · intro α
        obtain ⟨x, -, hx⟩ := hs α
        obtain ⟨y, -, hy⟩ := hs' α
        exact ⟨x + y, trivial, by rw [map_add, hx, hy, map_add]⟩
      · rw [comb_add]; convert hq' using 1; abel

  have divP : ∀ h : MvPowerSeries (Fin d) Q, QL μ (Ideal.span {(p : B)}) h →
      QL μ ⊤ ((↑u⁻¹ : Q) • h) ∧ h = (p : Q) • ((↑u⁻¹ : Q) • h) := by
    intro h ⟨h0, hl, hc⟩
    refine ⟨⟨?_, fun i => ?_, fun α => ?_⟩, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]
    · obtain ⟨t, ht, he'⟩ := hl i
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      simp only [lin, coeff_smul] at he' ⊢
      rw [he', ht']
    · obtain ⟨t, ht, he'⟩ := hc α
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      rw [formalCoboundary_smul hconst, coeff_smul, he', ht']
    · rw [smul_smul, ← hu, Units.mul_inv, one_smul]
  have E1 : ∀ f : {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, ∃ (b : ι → B) (s g : MvPowerSeries (Fin d) Q),
      In (⊤ : Ideal B) s ∧ QL μ ⊤ g ∧ f.1 = comb b e + s + (p : Q) • g := by
    intro ⟨f, hf⟩
    obtain ⟨b, s, hs, hq⟩ := chainE _ hch f hf
    obtain ⟨hg, hgq⟩ := divP _ hq
    exact ⟨b, s, _, hs, hg, by rw [← hgq]; abel⟩
  choose bF sF gF hsF hgF heqF using E1

  have V : ∀ α : Fin d →₀ ℕ, ∃ v : ℕ, ∀ g, QL μ ⊤ g → (p : Q) ^ v * coeff α g ∈ (algebraMap B Q).range := by
    intro α
    by_cases hα : α = 0
    · refine ⟨0, fun g hg => ⟨0, ?_⟩⟩
      rw [hα, coeff_zero_eq_constantCoeff_apply, hg.1]; simp
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push_neg at h; exact hα (Finsupp.ext fun i => by simp [h i])
      obtain ⟨v, n, hn, hαi⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Fact.out : p.Prime).one_lt.ne'
      have hcop : Nat.Coprime n p := Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)
      obtain ⟨w, hw⟩ := hF.unit_coprime n hcop
      refine ⟨v, fun g hg => ?_⟩
      obtain ⟨t, -, ht⟩ := GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hL ⊤ g hg α i
      refine ⟨↑w⁻¹ * t, ?_⟩
      rw [hαi] at ht
      push_cast at ht
      rw [map_mul, ← ht]
      have hw1 : algebraMap B Q (↑w⁻¹) * (n : Q) = 1 := by
        rw [← map_natCast (algebraMap B Q) n, ← map_mul, ← hw, Units.inv_mul, map_one]
      linear_combination ((p : Q) ^ v * coeff α g) * hw1

  have chainU : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), comb c e = s → ∀ N,
      Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → In (⊤ : Ideal B) s →
        (∀ i, c i ∈ N) ∧ In N s := by
    intro c s hcs N hN hs
    induction hN with
    | refl => exact ⟨fun _ => trivial, hs⟩
    | tail _ hst ih =>
      exact GlobalTheory.T.quasiLogarithm_devissage_step_independent p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst c s ih.1 ih.2
        (by rw [hcs, sub_self]; exact ql0 _)
  have U1 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∃ (c' : ι → B) (s' : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s' ∧ comb c' e = s' ∧
        ∀ i, c i = c' i * p := by
    intro c s hs hcs
    obtain ⟨hc, hsp⟩ := chainU c s hcs _ hch hs
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    refine ⟨c', (↑u⁻¹ : Q) • s, ?_, ?_, fun i => (hc' i).symm⟩
    · intro α
      obtain ⟨t, ht, h1⟩ := hsp α
      obtain ⟨t', h2⟩ := key t ht
      exact ⟨t', trivial, by rw [coeff_smul, h1, h2]⟩
    · have hc2 : c = fun i => c' i * p := funext fun i => (hc' i).symm
      rw [← hcs, hc2, comb_mul_right, smul_smul, hmapP, ← hu, Units.inv_mul, one_smul]
  have U2 : ∀ K (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∀ i, c i ∈ Ideal.span {(p : B) ^ K} := by
    intro K
    induction K with
    | zero => intro c s _ _ i; simp
    | succ K ih =>
      intro c s hs hcs i
      obtain ⟨c', s', hs', hcs', hc⟩ := U1 c s hs hcs
      rw [hc i, pow_succ]
      exact Ideal.mem_span_singleton.2 (mul_dvd_mul_right (Ideal.mem_span_singleton.1 (ih c' s' hs' hcs' i)) _)
  have U3 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → c = 0 := by
    intro c s hs hcs; funext i
    refine hF.complete.toIsHausdorff.haus (c i) fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hsm]; exact U2 n c s hs hcs i
  refine ⟨he, fun f hf => ?_⟩

  obtain ⟨Fs, hF0, hFs⟩ : ∃ Fs : ℕ → {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f},
      Fs 0 = ⟨f, hf⟩ ∧ ∀ k, Fs (k + 1) = ⟨gF (Fs k), hgF (Fs k)⟩ :=
    ⟨fun k => Nat.rec ⟨f, hf⟩ (fun _ y => ⟨gF y, hgF y⟩) k, rfl, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ι → B, ∀ K i, x K i = ∑ k ∈ Finset.range K, (p : B) ^ k * bF (Fs k) i :=
    ⟨_, fun _ _ => rfl⟩
  have hrec : ∀ K, ∃ S, In (⊤ : Ideal B) S ∧ f = comb (x K) e + S + (p : Q) ^ K • (Fs K).1 := by
    intro K
    induction K with
    | zero =>
      have hx0 : x 0 = 0 := funext fun i => by simp [hx]
      refine ⟨0, fun α => ⟨0, trivial, by simp⟩, ?_⟩
      rw [hx0, comb_zero, hF0]; simp
    | succ K ih =>
      obtain ⟨S, hS, hfe⟩ := ih
      refine ⟨S + (p : Q) ^ K • sF (Fs K), ?_, ?_⟩
      · intro α
        obtain ⟨a, -, ha⟩ := hS α
        obtain ⟨c, -, hc⟩ := hsF (Fs K) α
        exact ⟨a + p ^ K * c, trivial, by simp [coeff_smul, ha, hc, map_add, map_mul, map_pow, map_natCast]⟩
      · have h1 : x (K + 1) = x K + fun i => (p : B) ^ K * bF (Fs K) i := by
          funext i; simp [hx, Finset.sum_range_succ]
        have h2 : (Fs (K + 1)).1 = gF (Fs K) := by rw [hFs]
        rw [h1, comb_add, comb_mul, h2, map_pow, map_natCast]
        conv_lhs => rw [hfe, heqF (Fs K)]
        simp only [smul_add, smul_smul, ← pow_succ]
        abel
  have hcau : ∀ m n, m ≤ n → ∀ i, x n i - x m i ∈ Ideal.span {(p : B) ^ m} := by
    intro m n hmn i
    rw [hx, hx, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    exact Ideal.mem_span_singleton.2
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _)
  have hlim : ∀ i, ∃ L : B, ∀ n, x n i - L ∈ Ideal.span {(p : B) ^ n} := by
    intro i
    obtain ⟨L, hL'⟩ := hF.complete.toIsPrecomplete.prec (f := fun n => x n i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_sub]; exact neg_mem (hcau m n hmn i))
    exact ⟨L, fun n => by have := hL' n; rwa [SModEq.sub_mem, hsm] at this⟩
  choose L hLx using hlim
  have hIn : In (⊤ : Ideal B) (f - comb L e) := by
    intro α
    obtain ⟨v, hv⟩ := V α
    obtain ⟨S, hS, hfe⟩ := hrec v
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hLx i v)
    have hmem : coeff α (f - comb L e) ∈ (algebraMap B Q).range := by
      rw [hfe]
      have e1 : comb (x v) e + S + (p : Q) ^ v • (Fs v).1 - comb L e =
          (comb (x v) e - comb L e) + S + (p : Q) ^ v • (Fs v).1 := by abel
      rw [e1, ← comb_sub, map_add, map_add, coeff_comb, coeff_smul]
      refine add_mem (add_mem (Subring.sum_mem _ fun i _ => ?_) ?_) (hv _ (Fs v).2)
      · rw [show (x v - L) i = c i * (p : B) ^ v from (hc i).symm,
          show algebraMap B Q (c i * (p : B) ^ v) * coeff α (e i) =
            algebraMap B Q (c i) * ((p : Q) ^ v * coeff α (e i)) by
              rw [map_mul, map_pow, map_natCast, mul_assoc]]
        exact Subring.mul_mem _ ⟨c i, rfl⟩ (hv _ (he i))
      · obtain ⟨a, -, ha⟩ := hS α; exact ⟨a, ha.symm⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, trivial, hb.symm⟩
  refine ⟨L, hIn, fun y hy => ?_⟩
  have hs : In (⊤ : Ideal B) (comb (y - L) e) := by
    intro α
    obtain ⟨a, -, ha⟩ := hIn α
    obtain ⟨a', -, ha'⟩ := hy α
    refine ⟨a - a', trivial, ?_⟩
    rw [map_sub, ← ha, ← ha', ← map_sub, comb_sub]
    congr 1; abel
  exact sub_eq_zero.1 (U3 _ _ hs rfl)
