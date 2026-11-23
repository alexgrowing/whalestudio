import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible

open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

namespace CharacterBalance

open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ}
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) (hdN : N < D.d) :
    askD D N a t w = 0 := by
  classical
  unfold askD
  refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun g hg => ?_))
  have hg' := (Finset.mem_filter.1 hg).2.2
  simp only [Finset.mem_Icc] at hi
  apply max_zero_of_gt hw hN hg'
  have h1 : (D.d : ℝ) ≤ (D.d : ℝ) ^ i := by
    have : (1 : ℝ) ≤ D.d := by exact_mod_cast hD.d_prime.one_lt.le
    calc (D.d : ℝ) = (D.d : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (D.d : ℝ) ^ i := pow_le_pow_right₀ this hi.1
  have h2 : (N : ℝ) < D.d := by exact_mod_cast hdN
  linarith

lemma cardI (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) : (Nat.card (D.inertia D.d) : ℂ) = 2 := by
  classical
  rw [natCard_eq_filter]
  have : univ.filter (fun x => x ∈ D.inertia D.d) = ({0, sgc0} : Finset (E0 × H)) := by
    ext x; simp [hD.inertia_d]
  rw [this, Finset.card_pair (by unfold sgc0; intro h; have := congrArg (fun x : E0 × H => x.1.1) h; simp at this)]
  norm_num

lemma ounram (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (p i : ℕ) (hp : p.Prime) (h2 : p ∉ S0)
    (hd : p ≠ D.d) (hi : 1 ≤ i) (g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if i • D.frob p = g then 2 else 0 := by
  classical
  have := orthogonality_ramified D p i hp hi g
  rw [this, hD.unram p hp h2 hd]
  by_cases he : i • D.frob p = g
  · rw [if_pos he, if_pos (by rw [he, sub_self]; exact AddSubgroup.zero_mem _), AddSubgroup.card_bot]
    norm_num
  · rw [if_neg he, if_neg (by rw [AddSubgroup.mem_bot, sub_eq_zero]; exact fun e => he e.symm)]

lemma lunram (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∉ S0) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by
  have hR : ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) = ∑ i ∈ Icc 1 N,
      (if ¬ InPhi (i • D.frob p) then 2 * (Real.log p : ℂ) * ((max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0 : ℝ) : ℂ)
        else 0) := by
    unfold askP
    rw [Finset.sum_filter, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  rw [hR]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have e : ∀ g, Kc D (p ^ i) g = if i • D.frob p = g then 2 else 0 :=
    fun g => ounram D hD p i hp h2 hd hi1 g
  simp only [e, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp only [Fc, Nat.cast_pow, mul_zero] <;> ring

lemma lsplit (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∈ S0) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = 0 := by
  classical
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  rw [Finset.sum_eq_zero, mul_zero]
  intro g hg
  have hg' := (Finset.mem_filter.1 hg).2
  have e := orthogonality_ramified D p i hp hi1 g
  unfold Kc
  rw [e]
  have : ¬ (g - i • D.frob p ∈ D.inertia p) := by
    intro hm
    apply hg'
    have hx := hD.split_inertia p h2 _ hm
    have hf := inPhi_nsmul (hD.split_frob p h2) i
    have := inPhi_add hx hf
    simpa using this
  simp [this]

lemma ld (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) := by
  classical
  unfold askD
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have e := orthogonality_ramified D D.d i hD.d_prime hi1 g
  unfold Kc
  rw [e, cardI D hD]
  unfold Fc
  by_cases hφ : InPhi g
  · simp [hφ]
  · by_cases hm : g - i • D.frob D.d ∈ D.inertia D.d
    · simp [hφ, hm]
    · simp [hφ, hm]

lemma askExp (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) = (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ) := by
  classical
  set S := univ.filter (fun g : E0 × H => ¬ InPhi g) with hS
  have hA : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) *
        ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 N, (Λ n : ℂ) * ∑ g ∈ S, Kc D n g * Fc a t w n g := by
    calc _ = ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ∑ n ∈ Icc 1 N, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) := by
          simp only [Finset.mul_sum]
      _ = ∑ g ∈ S, ∑ n ∈ Icc 1 N, ∑ ψ : AddChar (E0 × H) ℂ, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) :=
          Finset.sum_congr rfl (fun g _ => Finset.sum_comm)
      _ = ∑ n ∈ Icc 1 N, ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, (1 / ((PhiSet (H := H)).card : ℂ)) *
          (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ))) :=
          Finset.sum_comm
      _ = _ := by
          simp only [Kc, Fc, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun g _ =>
            Finset.sum_congr rfl (fun ψ _ => by ring)))
  rw [hA]
  rw [sum_vonMangoldt_primePow N (fun n => ∑ g ∈ S, Kc D n g * Fc a t w n g) (by
    intro p i hp hi hgt
    refine Finset.sum_eq_zero (fun g hg => ?_)
    have hg' := (Finset.mem_filter.1 hg).2
    unfold Fc
    rw [max_zero_of_gt hw hN hg' (m := ((p ^ i : ℕ) : ℝ)) (by exact_mod_cast hgt)]
    simp)]
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hC : ∀ p ∈ P, (∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ S, Kc D (p ^ i) g * Fc a t w (p ^ i) g)
      = (if IsInert D p then ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) else 0)
        + (if p = D.d then ((Real.log D.d * askD D N a t w : ℝ) : ℂ) else 0) := by
    intro p hpP
    have hp : p.Prime := (Finset.mem_filter.1 hpP).2
    by_cases hd : p = D.d
    · subst hd
      rw [hS, ld D hD N a t w, if_neg (fun h => h.2.2.2.1 rfl), if_pos rfl, zero_add]
    · rw [if_neg hd, add_zero]
      by_cases h2 : p ∈ S0
      · rw [hS, lsplit D hD N a t w hp h2]
        rw [if_neg]
        rintro ⟨_, _, _, _, hc⟩
        exact hc (hD.split_frob p h2)
      · have h21 : p ≠ 2 := fun e => h2 (e ▸ hD.two_mem)
        have h22 : p ≠ D.q1 := fun e => h2 (e ▸ hD.q1_mem)
        rw [hS, lunram D hD N a t w hp h2 hd]
        by_cases hin : IsInert D p
        · rw [if_pos hin]
        · rw [if_neg hin]
          have hφ : InPhi (D.frob p) := by
            by_contra hc; exact hin ⟨hp, h21, h22, hd, hc⟩
          have : askP D N a t w p = 0 := by
            unfold askP
            rw [Finset.sum_eq_zero]
            intro i hi
            exact absurd (inPhi_nsmul hφ i) (Finset.mem_filter.1 hi).2
          rw [this]; simp
  rw [Finset.sum_congr rfl hC, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq']
  have hfilt : (range (N + 1)).filter (IsInert D) = P.filter (IsInert D) := by
    rw [hP, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩)
  unfold ASK
  rw [hfilt]
  push_cast
  congr 1
  by_cases hdP : D.d ∈ P
  · rw [if_pos hdP]
  · rw [if_neg hdP]
    have hdN : N < D.d := by
      by_contra hc
      exact hdP (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hD.d_prime⟩)
    rw [ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime D hD hw hN hdN]; simp

end CharacterBalance

theorem ch_balance {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) : (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w := by
  classical
  have hf0 := PB.phi_card_ne_zero (H := H)
  have hfr : ((PhiSet (H := H)).card : ℝ) ≠ 0 := by exact_mod_cast hf0
  rw [CharacterBalance.askExp D hD a t w hw N hN]
  have hin : ∀ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∀ ψ : AddChar (E0 × H) ℂ,
      starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g)))
        + starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' := (Finset.mem_filter.1 hg).2
    have hW := hw _ (partner_inPhi t hg')
    rw [sum_cut D ψ N a _ ha hW (hN _ (partner_inPhi t hg')), inner_eq D ell ψ a _ ha hW]; ring
  rw [Finset.sum_congr rfl (fun g hg => Finset.sum_congr rfl (fun ψ _ => hin g hg ψ))]
  simp only [Finset.sum_add_distrib, mul_add]
  have hDe : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
      ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g)))
      = De D ell a t w := by
    unfold De
    refine congrArg _ (Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun ψ _ => by ring)))
  rw [hDe]
  have hsplit : ∀ g : E0 × H, (∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (if ψ = 0 then
        ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ))
      = ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ) := by
    intro g
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : AddChar (E0 × H) ℂ)), if_pos rfl, AddChar.zero_apply,
      map_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hψ)]
  have hcol : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ))
      = ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * ell chC) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [← Finset.sum_mul, colour_sum ψ, if_neg (Finset.ne_of_mem_erase hψ)])]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.2 ⟨PB.chC_ne_zero (H := H), mem_univ _⟩)]
    ring
  have hreal : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ((a * Real.log a - a * Real.log (w (partner t g))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ))
      = ((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, PB.card_notPhi,
      ← Finset.mul_sum, PB.sum_partner t (fun ρ => Real.log (w ρ))]
    simp only [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib, hreal, hcol]
  unfold MAIN
  push_cast
  field_simp
  ring

end Deduction

end
