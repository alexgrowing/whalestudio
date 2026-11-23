import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DigAbs
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.Joints Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem gamR_zero_zero (P : ℕ) : gamR P 0 0 = 1 := by
  unfold gamR
  simp

theorem gamR_one_zero (be : ℕ) : gamR 1 0 be = 1 := by
  unfold gamR
  have : ((be.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [this]

theorem digQ (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type) [Fintype σ] (g rho : σ → ℕ)
    (hrho : ∀ v, rho v < p ^ g v) :
    (∀ be : σ → ℕ, (∏ v, gamR (p ^ g v) (rho v) (be v)) ≠ 0 ∧
      padicValRat p (∏ v, gamR (p ^ g v) (rho v) (be v)) = 0) ∧
    ∀ (inv : Bool) (c : ℕ), ∃ (T : Finset (σ → ℕ)) (q : (σ → ℕ) → ℚ),
      (∀ j ∈ T, ∑ k, j k ≤ 4 * c ∧ PadicGe p (q j) 0) ∧
      ∀ be : σ → ℕ, PadicGe p ((if inv then (∏ v, gamR (p ^ g v) (rho v) (be v))⁻¹
          else (∏ v, gamR (p ^ g v) (rho v) (be v))) - ∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ)) c := by
  obtain ⟨hA, hB⟩ := lemma_five_two_first_holds D p hp h5
  have hrho' : ∀ v, rho v < p ^ (g v - 1 + 1) := by
    intro v
    by_cases h : g v = 0
    · have h1 := hrho v
      rw [h, pow_zero] at h1
      have : rho v = 0 := by omega
      rw [this]
      exact pow_pos hp.pos _
    · have : g v - 1 + 1 = g v := by omega
      rw [this]
      exact hrho v
  obtain ⟨hU, _, hQ⟩ := hB σ (fun v => g v - 1) rho hrho'
  have hgam : ∀ (v : σ) (e' : ℕ), gamR (p ^ (g v - 1 + 1)) (rho v) e' =
      cUnit (p ^ (g v - 1 + 1)) e' * dUnit (p ^ (g v - 1 + 1)) e' (rho v) := by
    intro v e'
    unfold gamR
    have h1 : ((rho v).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h2 : (e'.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h3 : ((p ^ (g v - 1 + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    rw [hA (g v - 1) (rho v) e' (hrho' v)]
    have hne : ((rho v).factorial : ℚ) * (e'.factorial : ℚ) * ((p ^ (g v - 1 + 1)).factorial : ℚ) ^ e' ≠ 0 :=
      mul_ne_zero (mul_ne_zero h1 h2) (pow_ne_zero _ h3)
    rw [mul_assoc _ (cUnit _ _) _, mul_div_cancel_left₀ _ hne]
  have hkey : ∀ (be : σ → ℕ) (v : σ), gamR (p ^ (g v - 1 + 1)) (rho v) (if g v = 0 then 0 else be v) =
      gamR (p ^ g v) (rho v) (be v) := by
    intro be v
    by_cases h : g v = 0
    · have h1 := hrho v
      rw [h, pow_zero] at h1
      have h2 : rho v = 0 := by omega
      rw [if_pos h, h2, gamR_zero_zero, h, pow_zero, gamR_one_zero]
    · have : g v - 1 + 1 = g v := by omega
      rw [if_neg h, this]
  have hratio : ∀ e' : σ → ℕ,
      ((∏ k, (((rho k + p ^ (g k - 1 + 1) * e' k).factorial : ℕ) : ℚ)) /
        (∏ k, ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (g k - 1 + 1)).factorial : ℚ) ^ (e' k))) =
      ∏ k, gamR (p ^ (g k - 1 + 1)) (rho k) (e' k) := by
    intro e'
    rw [← Finset.prod_div_distrib]
    rfl
  refine ⟨fun be => ?_, fun inv c => ?_⟩
  · have h := hU (fun v => if g v = 0 then 0 else be v)
    have e1 : (∏ k, cUnit (p ^ (g k - 1 + 1)) (if g k = 0 then 0 else be k) *
        dUnit (p ^ (g k - 1 + 1)) (if g k = 0 then 0 else be k) (rho k)) = ∏ v, gamR (p ^ g v) (rho v) (be v) :=
      Finset.prod_congr rfl fun v _ => by rw [← hgam, hkey]
    rw [e1] at h
    exact h
  · obtain ⟨T, q, hT, hq⟩ := hQ inv c
    refine ⟨T.filter (fun j => ∀ k, g k = 0 → j k = 0), q, fun j hj => hT j (Finset.mem_filter.1 hj).1, fun be => ?_⟩
    have h := hq (fun v => if g v = 0 then 0 else be v)
    simp only [hratio] at h
    have e1 : (∏ k, gamR (p ^ (g k - 1 + 1)) (rho k) (if g k = 0 then 0 else be k)) =
        ∏ v, gamR (p ^ g v) (rho v) (be v) := Finset.prod_congr rfl fun v _ => hkey be v
    rw [e1] at h
    have e2 : ∑ j ∈ T, q j * ∏ k, (((if g k = 0 then 0 else be k).choose (j k) : ℕ) : ℚ) =
        ∑ j ∈ T.filter (fun j => ∀ k, g k = 0 → j k = 0), q j * ∏ k, ((be k).choose (j k) : ℚ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : g k = 0
        · rw [if_pos hk, hj k hk]; simp
        · rw [if_neg hk]
      · push Not at hj
        obtain ⟨k, hk, hjk⟩ := hj
        have : ∏ k, (((if g k = 0 then 0 else be k).choose (j k) : ℕ) : ℚ) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
          rw [if_pos hk]
          have : Nat.choose 0 (j k) = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjk)
          rw [this]; simp
        rw [this, mul_zero]
    rw [e2] at h
    exact h

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem binomCombF_onFinset {σ : Type} [Fintype σ] (T : Finset (σ → ℕ)) (o : (σ → ℕ) → O) :
    ∃ lam : (σ →₀ ℕ) →₀ O, (∀ m ∈ lam.support, (⇑m : σ → ℕ) ∈ T) ∧
      ∀ be : σ →₀ ℕ, binomCombF (K := KK O) lam be =
        ∑ j ∈ T, algebraMap O (KK O) (o j) * ∏ k, (((be k).choose (j k) : ℕ) : KK O) := by
  let em : (σ → ℕ) ↪ (σ →₀ ℕ) := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).symm.toEmbedding
  have hem : ∀ j : σ → ℕ, (⇑(em j) : σ → ℕ) = j := fun j => by
    funext k
    rfl
  have hsub : ∀ m : σ →₀ ℕ, (if (⇑m : σ → ℕ) ∈ T then o ⇑m else 0) ≠ 0 → m ∈ T.map em := by
    intro m hm
    by_cases hT : (⇑m : σ → ℕ) ∈ T
    · refine Finset.mem_map.2 ⟨⇑m, hT, ?_⟩
      ext k
      rfl
    · simp [hT] at hm
  refine ⟨Finsupp.onFinset (T.map em) (fun m => if (⇑m : σ → ℕ) ∈ T then o ⇑m else 0) hsub, fun m hm => ?_, fun be => ?_⟩
  · have h1 := Finsupp.mem_support_iff.1 hm
    rw [Finsupp.onFinset_apply] at h1
    by_contra hT
    simp [hT] at h1
  · unfold binomCombF
    rw [Finset.sum_subset (Finsupp.support_onFinset_subset)]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finsupp.onFinset_apply, hem, if_pos hj]
      congr 1
      rw [← Finset.prod_subset (Finset.subset_univ (em j).support)]
      · intro k _ hk
        have h0 : j k = 0 := by
          have := Finsupp.notMem_support_iff.1 hk
          exact this
        rw [h0]; simp
    · intro m _ hm
      rw [Finsupp.notMem_support_iff.1 hm]
      simp

theorem digAbs (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (S : UniformizedDVR p O) : DigAbs p O := by
  intro σ _ g rho hrho
  have hO : CharZero O := dvr_ring_charZero hp S
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  obtain ⟨h1, h2⟩ := digQ D p hp h5 σ g rho hrho
  refine ⟨fun be => h1 be, fun inv c => ?_⟩
  obtain ⟨T, q, hT, hq⟩ := h2 inv c
  have hex : ∀ j, ∃ o : O, j ∈ T → ((q j : ℚ) : KK O) = algebraMap O (KK O) o := by
    intro j
    by_cases hj : j ∈ T
    · obtain ⟨o, ho⟩ := rat_padicGe_cast hp S (q j) 0 (by simpa using (hT j hj).2)
      exact ⟨o, fun _ => by simpa using ho⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose o ho using hex
  obtain ⟨lam, hsup, hlam⟩ := binomCombF_onFinset (O := O) T o
  refine ⟨lam, fun m hm => ?_, fun be => ?_⟩
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact (hT _ (hsup m hm)).1
  · obtain ⟨z, hz⟩ := rat_padicGe_cast hp S _ c (hq be)
    have hsum : binomCombF (K := KK O) lam be =
        ((∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ) : ℚ) : KK O) := by
      rw [hlam be]
      push_cast
      exact Finset.sum_congr rfl fun j hj => by rw [ho j hj]
    have heq : ((if inv = true then (((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O))⁻¹
          else ((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O)) - binomCombF (K := KK O) lam be) =
        (p : KK O) ^ c * algebraMap O (KK O) z := by
      rw [← hz, hsum]
      cases inv <;> simp
    rw [heq]
    exact geQ_vK_pow_mul S c z

theorem exists_unit_of_rat (p : ℕ) (hp : p.Prime) (S : UniformizedDVR p O) (x : ℚ) (hx : x ≠ 0) (hv : padicValRat p x = 0) :
    ∃ u : O, IsUnit u ∧ algebraMap O (KK O) u = ((x : ℚ) : KK O) := by
  have hO : CharZero O := dvr_ring_charZero hp S
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := rat_padicGe_cast hp S x 0 (Or.inr (by rw [hv]; simp))
  obtain ⟨b, hb⟩ := rat_padicGe_cast hp S x⁻¹ 0 (Or.inr (by rw [padicValRat.inv, hv]; simp))
  rw [pow_zero, one_mul] at ha hb
  refine ⟨a, ?_, ha.symm⟩
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul, ← ha, ← hb, map_one]
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hx)
  exact IsUnit.of_mul_eq_one b hab

theorem gaAt (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (S : UniformizedDVR p O) {n' r K : ℕ} [NeZero n'] [NeZero r]
    [NeZero K] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) : GaAt (K := K) p O Fr nL := by
  intro rho hrho
  have hDA := digAbs (O := O) D p hp h5 S
  obtain ⟨hn1, _⟩ := hDA (TL J nL r × Fin K) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.natAdd r v.2)) (fun v => hrho v.1 _)
  obtain ⟨hp1, hp2⟩ := hDA (TL J nL r × Fin r) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.castAdd K v.2)) (fun v => hrho v.1 _)
  refine ⟨fun bn => hn1 bn, fun bp => hp1 bp, ?_⟩
  have hex : ∀ al : TL J nL r × Fin r →₀ ℕ, ∃ u : O, IsUnit u ∧
      algebraMap O (KK O) u = ((gamPl Fr p nL rho al : ℚ) : KK O) :=
    fun al => exists_unit_of_rat p hp S _ (hp1 al).1 (hp1 al).2
  choose ga hu hga using hex
  refine ⟨ga, hu, hga, fun k _ ε => ?_⟩
  obtain ⟨lam, hl1, hl2⟩ := hp2 (!ε) k
  refine ⟨lam, fun m hm => le_trans (hl1 m hm) (by omega), fun al => ?_⟩
  have h := hl2 al
  rw [hga al]
  have hdef : gamPl Fr p nL rho al =
      ∏ v : TL J nL r × Fin r, gamR (p ^ Fr.dist (segZ v.1.1) (posTL Fr v.1)) (rho (v.1, Fin.castAdd K v.2)) (al v) := rfl
  rw [hdef]
  cases ε
  · simpa using h
  · simpa using h

end Formalism.MainNotions.Proposition5Numerics
