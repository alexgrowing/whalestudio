import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.YmDerivSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def w0c : Lc X la w := w0inv X la w

def NoRow0 (β : Idx D j N →₀ ℕ) : Prop := ∀ k, β (0, k) = 0

theorem section_mul_inverse_completion :
    algebraMap (Rp X la N) (Lc X la w) (sec X la w 0) * w0c X la w = 1 :=
  section_mul_inverse_eq_one X la w

theorem coe_sfr_Lc (i : Fin (WeightFamilies.dimY D j + 1)) :
    ((sfr X la w i : ↥(Frac0 X la w)) : Lw X la w) =
      algebraMap (Rp X la N) (Lc X la w) (sec X la w i) * w0c X la w := by
  rw [coe_sfr, frac_apply, pow_one]
  rfl

theorem hasse_section_eq_zero {β : Idx D j N →₀ ℕ} (hβ : NoRow0 β) (h0 : β ≠ 0) :
    hasseRp X la N β (sec X la w 0) = 0 := by
  rw [hasseRp_sec]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hasseOp_Tv, if_neg h0, if_neg, map_zero, zero_smul]
  intro e
  have := hβ k
  rw [e, Finsupp.single_eq_same] at this
  exact one_ne_zero this

theorem hasse_sfr {β : Idx D j N →₀ ℕ} (hβ : NoRow0 β) (i : Fin (WeightFamilies.dimY D j + 1)) :
    hasse X la w β ((sfr X la w i : ↥(Frac0 X la w)) : Lw X la w) =
      algebraMap (Rp X la N) (Lc X la w) (hasseRp X la N β (sec X la w i)) * w0c X la w := by
  rw [coe_sfr_Lc]
  have hy : algebraMap (Rp X la N) (Lc X la w) (sec X la w 0) *
      (algebraMap (Rp X la N) (Lc X la w) (sec X la w i) * w0c X la w) =
      algebraMap (Rp X la N) (Lc X la w) (sec X la w i) := by
    rw [mul_left_comm, section_mul_inverse_completion, mul_one]
  have h := hasse_of_mul_eq X la w β hy
  rw [Finset.sum_eq_single ((0 : Idx D j N →₀ ℕ), β)] at h
  · rw [hasseRp_zero] at h
    dsimp only at h
    calc hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (sec X la w i) * w0c X la w)
        = (algebraMap (Rp X la N) (Lc X la w) (sec X la w 0) * w0c X la w) *
            hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (sec X la w i) * w0c X la w) := by
          rw [section_mul_inverse_completion, one_mul]
      _ = _ := by rw [mul_comm (algebraMap _ _ _) (w0c X la w), mul_assoc, h, mul_comm]
  · rintro ⟨q1, q2⟩ hq hne
    rw [mem_antidiagonal] at hq
    dsimp only at hq
    have hq1 : q1 ≠ 0 := by
      rintro rfl
      apply hne
      rw [zero_add] at hq
      rw [hq]
    have hn : NoRow0 q1 := fun k => by
      have h1 := congrArg (fun f : Idx D j N →₀ ℕ => f (0, k)) hq
      simp only [Finsupp.add_apply] at h1
      have h2 := hβ k
      omega
    rw [hasse_section_eq_zero X la w hn hq1, map_zero, zero_mul]
  · intro h'
    exact absurd (mem_antidiagonal.2 (zero_add β)) h'

end

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem bcol_apply {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) (p : Idx D j N) :
    PoleLengthBounds.bcol jj α p = if p.2 = jj then Fin.cases (motive := fun _ => ℕ) 0 α p.1 else 0 := rfl

theorem bcol_noRow0 {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) : NoRow0 (PoleLengthBounds.bcol jj α) := fun k => by
  rw [bcol_apply]
  split_ifs <;> rfl

theorem bcol_sub_single {N : ℕ} (jj : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) (l : Fin (WeightFamilies.dimY D j)) :
    PoleLengthBounds.bcol jj α - Finsupp.single (l.succ, jj) 1 = PoleLengthBounds.bcol jj (α - Pi.single l 1) := by
  ext ⟨i, k⟩
  rw [Finsupp.tsub_apply, bcol_apply, bcol_apply, Finsupp.single_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · have : ((l.succ, jj) : Idx D j N) ≠ (0, k) := fun e => Fin.succ_ne_zero l (congrArg Prod.fst e)
    simp [this]
  · by_cases hk : k = jj
    · subst hk
      by_cases hi : i = l
      · subst hi; simp
      · have : ((l.succ, k) : Idx D j N) ≠ (i.succ, k) := fun e => hi (Fin.succ_injective _ (congrArg Prod.fst e)).symm
        simp [this, Pi.single_apply, hi]
    · have : ((l.succ, jj) : Idx D j N) ≠ (i.succ, k) := fun e => hk (congrArg Prod.snd e).symm
      simp [this, hk]

theorem sum_add_single {d : ℕ} (δ : Fin d → ℕ) (l : Fin d) :
    ∑ i, (δ + Pi.single l 1 : Fin d → ℕ) i = ∑ i, δ i + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]

theorem eq_sub_add_single {d : ℕ} (δ : Fin d → ℕ) (l : Fin d) (h : 1 ≤ δ l) :
    δ = (δ - Pi.single l 1) + Pi.single l 1 := by
  funext i
  by_cases hi : i = l
  · subst hi; simp; omega
  · simp [Pi.single_apply, hi]

theorem sub_single_of_zero {d : ℕ} (δ : Fin d → ℕ) (l : Fin d) (h : δ l = 0) : δ - Pi.single l 1 = δ := by
  funext i
  by_cases hi : i = l
  · subst hi; simp [h]
  · simp [Pi.single_apply, hi]

theorem coe_wfr_Lc (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) :
    ((PoleLengthBounds.wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lc X la G.w) (emb X la G.N (X.inc wL (G.w jj))) * w0c X la G.w := by
  simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one] <;> rfl

theorem hasse_single_sfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N)
    (l : Fin (WeightFamilies.dimY D j)) :
    hasse X la G.w (Finsupp.single ((l.succ, jj) : Idx D j G.N) 1)
        ((sfr X la G.w l.succ : ↥(Frac0 X la G.w)) : Lw X la G.w) =
      ((PoleLengthBounds.wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) := by
  have hn : NoRow0 (Finsupp.single ((l.succ, jj) : Idx D j G.N) 1) := fun k => by
    rw [Finsupp.single_apply, if_neg]
    exact fun e => Fin.succ_ne_zero l (congrArg Prod.fst e)
  rw [hasse_sfr X la G.w hn, hasseRp_single, pdRp_sec, if_pos rfl, coe_wfr_Lc]

theorem hasse_sfr_eq_zero (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N)
    (α : Fin (WeightFamilies.dimY D j) → ℕ) (l : Fin (WeightFamilies.dimY D j)) {c : Idx D j G.N →₀ ℕ}
    (hc : ∀ p, c p ≤ PoleLengthBounds.bcol jj α p) (h0 : c ≠ 0) (he : c ≠ Finsupp.single (l.succ, jj) 1) :
    hasse X la G.w c ((sfr X la G.w l.succ : ↥(Frac0 X la G.w)) : Lw X la G.w) = 0 := by
  have hn : NoRow0 c := fun k => by
    have := hc (0, k)
    rw [bcol_noRow0 jj α k] at this
    omega
  rw [hasse_sfr X la G.w hn]
  by_cases h1 : ∃ p, c = Finsupp.single p 1
  · obtain ⟨p, rfl⟩ := h1
    rw [hasseRp_single, pdRp_sec]
    by_cases hp : p.1 = l.succ
    · exfalso
      have hp2 : p.2 = jj := by
        by_contra hne
        have := hc p
        rw [Finsupp.single_eq_same, bcol_apply, if_neg hne] at this
        omega
      exact he (by rw [show p = (l.succ, jj) from Prod.ext hp hp2])
    · rw [if_neg hp, map_zero, zero_mul]
  · push Not at h1
    rw [hasseRp_sec_eq_zero X la G.w h0 h1, map_zero, zero_mul]

theorem ymDeriv : PoleLengthBounds.YmDeriv := by
  intro D B P j X ka wL wF G la jj
  suffices H : ∀ (s : ℕ) (γ α : Fin (WeightFamilies.dimY D j) → ℕ), ∑ i, γ i = s → s ≤ ∑ i, α i →
      hasse X la G.w (PoleLengthBounds.bcol jj α) ((PoleLengthBounds.ym G la γ : ↥(Frac0 X la G.w)) : Lw X la G.w) =
        if γ = α then ((PoleLengthBounds.wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) ^ (∑ i, α i) else 0 from
    fun γ α h => H _ γ α rfl h
  intro s
  induction s with
  | zero =>
    intro γ α hγ _
    have hγ0 : γ = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.1 hγ) i (Finset.mem_univ i)
    subst hγ0
    have hym : PoleLengthBounds.ym G la 0 = 1 := by simp [PoleLengthBounds.ym]
    rw [hym, OneMemClass.coe_one]
    by_cases hα : α = 0
    · subst hα
      have hb : PoleLengthBounds.bcol jj (0 : Fin (WeightFamilies.dimY D j) → ℕ) = 0 := by
        ext ⟨i, k⟩
        rw [bcol_apply]
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [hb, if_pos rfl]
      refine (hasse_zero X la G.w _).trans ?_
      simp
      rfl
    · have hb : PoleLengthBounds.bcol jj α ≠ 0 := by
        intro h
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hα
        have := congrArg (fun f : Idx D j G.N →₀ ℕ => f (i.succ, jj)) h
        simp only [bcol_apply, Fin.cases_succ, Finsupp.coe_zero, Pi.zero_apply] at this
        exact hi this
      rw [if_neg (Ne.symm hα)]
      have := hasse_emb X la G.w hb 1
      rw [map_one, map_one] at this
      exact this
  | succ s ih =>
    intro γ α hγ hs
    obtain ⟨l, hl⟩ : ∃ l, 1 ≤ γ l := by
      by_contra hc
      push Not at hc
      have : ∑ i, γ i = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
      omega
    obtain ⟨γ', rfl⟩ : ∃ γ' : Fin (WeightFamilies.dimY D j) → ℕ, γ = γ' + Pi.single l 1 := ⟨_, eq_sub_add_single γ l hl⟩
    have hγ's : ∑ i, γ' i = s := by
      have := sum_add_single γ' l
      omega
    have hym : PoleLengthBounds.ym G la (γ' + Pi.single l 1) = sfr X la G.w l.succ * PoleLengthBounds.ym G la γ' :=
      PoleLengthBounds.prod_pow_add_single (fun i => sfr X la G.w i.succ) γ' l
    rw [hym, MulMemClass.coe_mul]
    refine (hasse_mul X la G.w (PoleLengthBounds.bcol jj α) _ _).trans ?_
    have hIHa : hasse X la G.w (PoleLengthBounds.bcol jj α) ((PoleLengthBounds.ym G la γ' : ↥(Frac0 X la G.w)) : Lw X la G.w) = 0 := by
      rw [ih γ' α hγ's (by omega), if_neg]
      · rfl
      · rintro rfl
        omega
    have hsα : s ≤ ∑ i, (α - Pi.single l 1 : Fin (WeightFamilies.dimY D j) → ℕ) i := by
      have h1 : ∑ i, α i ≤ ∑ i, ((α - Pi.single l 1) + Pi.single l 1 : Fin (WeightFamilies.dimY D j) → ℕ) i :=
        Finset.sum_le_sum fun i _ => le_tsub_add
      rw [sum_add_single] at h1
      omega
    have hIHb := ih γ' (α - Pi.single l 1) hγ's hsα
    have tb : hasse X la G.w (Finsupp.single ((l.succ, jj) : Idx D j G.N) 1)
          ((sfr X la G.w l.succ : ↥(Frac0 X la G.w)) : Lw X la G.w) *
        hasse X la G.w (PoleLengthBounds.bcol jj α - Finsupp.single ((l.succ, jj) : Idx D j G.N) 1)
          ((PoleLengthBounds.ym G la γ' : ↥(Frac0 X la G.w)) : Lw X la G.w) =
        if γ' + Pi.single l 1 = α then ((PoleLengthBounds.wfr G la jj : ↥(Frac0 X la G.w)) : Lw X la G.w) ^ (∑ i, α i) else 0 := by
      rw [hasse_single_sfr, bcol_sub_single, hIHb]
      by_cases hγα : γ' + Pi.single l 1 = α
      · have hγ'α : γ' = α - Pi.single l 1 := by
          rw [← hγα]
          funext i
          simp
        rw [if_pos hγ'α, if_pos hγα, ← hγ'α, ← hγα, sum_add_single, pow_succ']
        rfl
      · rw [if_neg hγα, if_neg]
        · exact mul_zero _
        intro h
        apply hγα
        by_cases hal : 1 ≤ α l
        · rw [eq_sub_add_single α l hal, ← h]
        · exfalso
          have hα0 : α l = 0 := by omega
          rw [sub_single_of_zero α l hα0] at h
          subst h
          omega
    have hne : (((0 : Idx D j G.N →₀ ℕ), PoleLengthBounds.bcol jj α) : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ)) ≠
        (Finsupp.single ((l.succ, jj) : Idx D j G.N) 1,
          PoleLengthBounds.bcol jj α - Finsupp.single ((l.succ, jj) : Idx D j G.N) 1) := fun h =>
      (Finsupp.single_ne_zero.2 one_ne_zero) (congrArg Prod.fst h).symm
    rw [Finset.sum_eq_add _ _ hne]
    · dsimp only
      rw [hIHa, mul_zero, zero_add]
      exact tb
    · rintro ⟨c1, c2⟩ hc ⟨h1, h2⟩
      rw [mem_antidiagonal] at hc
      dsimp only at hc ⊢
      have hc1 : c1 ≠ 0 := by
        rintro rfl
        apply h1
        rw [zero_add] at hc
        rw [hc]
      have hce : c1 ≠ Finsupp.single ((l.succ, jj) : Idx D j G.N) 1 := by
        rintro rfl
        apply h2
        rw [← hc, add_tsub_cancel_left]
      have hle : ∀ p, c1 p ≤ PoleLengthBounds.bcol jj α p := fun p => by
        have := congrArg (fun f : Idx D j G.N →₀ ℕ => f p) hc
        simp only [Finsupp.add_apply] at this
        omega
      rw [hasse_sfr_eq_zero G la jj α l hle hc1 hce, zero_mul]
    · intro h
      exact absurd (mem_antidiagonal.2 (zero_add _)) h
    · intro hnot
      dsimp only
      rw [tb, if_neg]
      · rfl
      intro hγα
      apply hnot
      apply mem_antidiagonal.2
      dsimp only
      refine add_tsub_cancel_of_le (Finsupp.single_le_iff.2 ?_)
      rw [bcol_apply, if_pos rfl, Fin.cases_succ, ← hγα]
      simp

end PI.PoleLengthCount
