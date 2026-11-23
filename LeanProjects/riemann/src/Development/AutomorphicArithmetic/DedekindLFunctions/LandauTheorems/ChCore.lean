import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChBalance

open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

namespace CharacterBalanceMoves

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def e1 (h : H) : E0 × H := (((1 : ZMod 2), (0 : ZMod 2)), h)

def Th (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (b y : ℝ) (u0 t : H) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ s ∈ T2, ∑ ψ : AddChar (E0 × H) ℂ,
    ψ (-(e1 (s + u0 - t))) * ((b : ℂ) * GPsi D ell ψ y)

lemma mem_psi (A0 : AddSubgroup H) (ψ : AddChar (E0 × H) ℂ) : ψ ∈ PsiA A0 ↔ ∀ s ∈ A0, ψ (0, s) = 1 := by
  classical
  unfold PsiA
  rw [Finset.mem_filter]
  simp

lemma sum_A (A0 : AddSubgroup H) [Fintype A0] (ψ : AddChar (E0 × H) ℂ) (s t : H) (hs : s ∈ A0) :
    ∑ u : A0, ψ (-(e1 (s + (u : H) - t))) = if ψ ∈ PsiA A0 then (Fintype.card A0 : ℂ) * ψ (e1 t) else 0 := by
  have hg : ∀ u : A0, (-(e1 (s + (u : H) - t)) : E0 × H) = e1 t + (0, -s) + (0, -(u : H)) := by
    intro u
    ext
    · simp [e1]
    · simp [e1]
    · simp [e1]; abel
  simp_rw [hg, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum]
  split_ifs with h
  · have h' := (mem_psi A0 ψ).1 h
    rw [h' _ (A0.neg_mem hs), Finset.sum_congr rfl (fun (u : A0) _ => h' _ (A0.neg_mem u.2))]
    simp [mul_comm]
  · let φ : AddChar A0 ℂ := ψ.compAddMonoidHom ((AddMonoidHom.inr E0 H).comp A0.subtype)
    have hφ : ∀ u : A0, φ u = ψ (0, (u : H)) := fun u => rfl
    have hne : φ ≠ 0 := by
      intro h0
      apply h
      rw [mem_psi]
      intro v hv
      rw [← hφ ⟨v, hv⟩, h0, AddChar.zero_apply]
    have h1 := AddChar.sum_eq_zero_iff_ne_zero.2 hne
    have h2 : ∑ u : A0, ψ (0, -(u : H)) = ∑ u : A0, φ u := by
      rw [← Equiv.sum_comp (Equiv.neg A0) φ]
      rfl
    rw [h2, h1, mul_zero]

lemma sum_Th (A0 : AddSubgroup H) [Fintype A0] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (b y : ℝ) (t : H) :
    ∑ u : A0, Th D ell T2 b y u t
      = (((Fintype.card A0 : ℝ) * (b * (delta2 T2 / 2)) : ℝ) : ℂ) * ∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ y := by
  unfold Th
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ s ∈ T2, ∑ u : A0, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-(e1 (s + (u : H) - t))) * ((b : ℂ) * GPsi D ell ψ y)
      = ((Fintype.card A0 : ℂ) * b) * ∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ y := by
    intro s hs
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_A A0 _ s t (hT2 s hs), ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, phiSet_card]
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold delta2
  push_cast
  field_simp

lemma th_le (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (x b b' η X' θ A : ℝ) (u0 t : H) (w : E0 × H → ℝ)
    (hx : 3 ≤ x) (hb : 0 < b) (hη : 0 ≤ η) (hX' : 0 < X') (_hb' : 0 < b') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ)
    (hA : |A / b - x| ≤ 1) (hwpos : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hwthick : ∀ ρ, IsThickAt T2 u0 ρ → b ≤ w ρ ∧ w ρ ≤ b + η + 1)
    (hwthin : ∀ ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w ρ ≤ 2 * b')
    (hThin : ThinScales D ell X' θ) (hLip : LipW D ell) :
    (Th D ell T2 b (A / b) u0 t).re ≤ (De D ell A t w).re + 2 * fPl H * (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hA
  have hA1 : (x - 1) * b ≤ A := by
    have : x - 1 ≤ A / b := by linarith
    rwa [le_div_iff₀ hb] at this
  have hA2 : A ≤ (x + 1) * b := by
    have : A / b ≤ x + 1 := by linarith
    rwa [div_le_iff₀ hb] at this
  have hA0 : 0 < A := lt_of_lt_of_le (by nlinarith) hA1
  have hTh : Th D ell T2 b (A / b) u0 t = (1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0) := by
    unfold Th
    congr 1
    have : ∀ g : E0 × H, ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0)
        = if IsThickAt T2 u0 (cconj + g + topPl t) then
          ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((b : ℂ) * GPsi D ell ψ (A / b)) else 0 := by
      intro g
      split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_filter, thick_filter,
      Finset.sum_image (fun s _ s' _ h => thick_inj u0 t (Set.mem_univ s) (Set.mem_univ s') h)]
    rfl
  have hn := CR.norm_avg_le (univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))) (CR.card_S_le t _ (Finset.Subset.refl _))
    (fun g ψ => ((w (cconj + g + topPl t) : ℝ) : ℂ) * GPsi D ell ψ (A / w (cconj + g + topPl t))
      - (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0))
    (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) (by positivity) (by
      intro g hg ψ
      have hρ := CR.partner_inPhi t (Finset.mem_filter.1 hg).2
      have hw0 := hwpos _ hρ
      have p1 : 0 ≤ 3 * (x + 1) * (η + 1) := by positivity
      have p2 : 0 ≤ (x + 1) * b * θ := by positivity
      by_cases hth : IsThickAt T2 u0 (cconj + g + topPl t)
      · simp only [if_pos hth]
        obtain ⟨k1, k2⟩ := hwthick _ hth
        have hl := hLip ψ A (w (cconj + g + topPl t)) b hA0 hw0 hb
        rw [min_eq_right k1, abs_of_nonneg (by linarith)] at hl
        have e1 : 3 * A / b ≤ 3 * (x + 1) := by
          rw [div_le_iff₀ hb]; nlinarith
        have e2 : 3 * A / b * (w (cconj + g + topPl t) - b) ≤ 3 * (x + 1) * (η + 1) :=
          mul_le_mul e1 (by linarith) (by linarith) (by positivity)
        linarith
      · simp only [if_neg hth, sub_zero]
        have hw2 := hwthin _ hρ hth
        have hy : X' / 3 ≤ A / w (cconj + g + topPl t) := by
          rw [le_div_iff₀ hw0]
          have k1 : X' / 3 * w (cconj + g + topPl t) ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          nlinarith
        have ht' := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        have : w (cconj + g + topPl t) * ‖GPsi D ell ψ (A / w (cconj + g + topPl t))‖ ≤ (x + 1) * b * θ :=
          calc w (cconj + g + topPl t) * ‖GPsi D ell ψ (A / w (cconj + g + topPl t))‖
            ≤ w (cconj + g + topPl t) * (A / w (cconj + g + topPl t) * θ) :=
              mul_le_mul_of_nonneg_left ht' hw0.le
          _ = A * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right hA2 hθ
        linarith)
  have hre := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) hn)).1
  have e : (De D ell A t w).re - (Th D ell T2 b (A / b) u0 t).re = ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (((w (cconj + g + topPl t) : ℝ) : ℂ) * GPsi D ell ψ (A / w (cconj + g + topPl t))
      - (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0))).re := by
    rw [CR.De_re, hTh]
    unfold balTop
    rw [← Complex.sub_re, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg Complex.re (congrArg _ (Finset.sum_congr rfl fun g _ => ?_))
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by rw [CR.GC_host]; ring
  rw [← e] at hre
  linarith

lemma move (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x Cd y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (ψ : AddChar (E0 × H) ℂ) (hψ0 : ψ ≠ 0) :
    ‖GPsi D ell ψ y - GPsi D ell ψ x‖ ≤ Real.log (x + 1) + Cd + ‖ell ψ‖ := by
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hd := hDer.1 ψ hψ0 y x (by linarith) (by linarith)
  have hmax : max y x ≤ x + 1 := max_le (by linarith) (by linarith)
  have hmax1 : 1 ≤ max y x := le_trans (by linarith) (le_max_right y x)
  have hlog : Real.log (max y x) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hmax
  have hlog0 : 0 ≤ Real.log (max y x) := Real.log_nonneg hmax1
  have hs : 0 ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by positivity
  have h1 := mul_le_mul_of_nonneg_right hy hs
  linarith

lemma triv (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x Cd : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hDer : DerivInt D ell Cd) (ψ : AddChar (E0 × H) ℂ) (hψ0 : ψ ≠ 0) :
    ‖GPsi D ell ψ x‖ ≤ x * (Real.log x + Cd + ‖ell ψ‖) := by
  have hd := hDer.1 ψ hψ0 x 1 (by linarith) le_rfl
  have h1 : GPsi D ell ψ 1 = ell ψ := by
    unfold GPsi
    rw [if_neg hψ0]
    simp
  rw [h1, max_eq_left (by linarith), abs_of_nonneg (by linarith)] at hd
  have h2 : ‖GPsi D ell ψ x‖ ≤ ‖GPsi D ell ψ x - ell ψ‖ + ‖ell ψ‖ := by
    simpa using norm_add_le (GPsi D ell ψ x - ell ψ) (ell ψ)
  have h3 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith

open Classical in

def vv (Kp : Finset (AddChar (E0 × H) ℂ)) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (c x : ℝ)
    (ψ : AddChar (E0 × H) ℂ) : ℝ :=
  if ψ ∈ Kp then wtA c ψ * (GPsi D ell ψ x).re else -‖GPsi D ell ψ x‖

lemma sum_vv (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (hKp : ∀ ψ ∈ Kp, ψ ∈ PsiA A0)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (c x : ℝ) :
    ∑ ψ ∈ PsiA A0, vv Kp D ell c x ψ = GmA D ell Kp c x - SigA D ell A0 Kp x := by
  classical
  unfold vv GmA SigA
  rw [Finset.sum_ite, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ψ
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hKp ψ h, h⟩⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_sdiff]

lemma one_char (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (y : H → ℝ)
    {x Cd c ρ Ko L R : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd) (hy : ∀ t ∈ TT, |y t - x| ≤ 1) (hDer : DerivInt D ell Cd)
    (hρ : 0 ≤ ρ) (hKo : 0 ≤ Ko) (h0K : 0 ∈ Kp) (hsg : ∀ ψ ∈ Kp, ψ sgc0 = 1)
    (h2 : ∀ ψ ∈ Kp, (¬ ∀ h : H, ψ (0, h) = 1) → ‖(∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)‖ ≤ ρ * (TT.card : ℝ))
    (hK : ∀ ψ ∈ Kp, ψ ≠ 0 → ‖ell ψ‖ ≤ Ko)
    (h3 : ∀ ψ ∈ PsiA A0, ψ ∉ Kp → ‖ell ψ‖ ≤ L)
    (r1 : Cd ≤ R) (r2 : Real.log (x + 1) + Cd + Ko + ρ * (x * (Real.log x + Cd + Ko)) ≤ R)
    (r3 : Real.log (x + 1) + Cd + L ≤ R)
    (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ∈ PsiA A0) :
    (TT.card : ℝ) * (vv Kp D ell c x ψ - R) ≤ ∑ t ∈ TT, (ψ (e1 t) * GPsi D ell ψ (y t)).re := by
  classical
  by_cases h0 : ψ = 0
  · subst h0
    have hw : wtA c (0 : AddChar (E0 × H) ℂ) = 1 := by
      unfold wtA
      rw [if_pos (fun _ => AddChar.zero_apply _)]
    unfold vv
    rw [if_pos h0K, hw, one_mul, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨hy1, hy2⟩ := abs_le.1 (hy t ht)
    have hG := hDer.2 (y t) x (by linarith) (by linarith)
    have hG' := mul_le_mul_of_nonneg_left (hy t ht) hCd
    have := (abs_le.1 (hG.trans hG')).1
    simp [GPsi]
    linarith
  by_cases hX : ψ ∈ Kp
  · unfold vv
    rw [if_pos hX]
    have h2' : ‖(∑ t ∈ TT, ψ (0, t)) - ((wtA c ψ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤ ρ * (TT.card : ℝ) := by
      unfold wtA
      split_ifs with h
      · simp only [h, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.ofReal_one, one_mul, sub_self, norm_zero]
        positivity
      · exact h2 ψ hX h
    generalize wtA c ψ = c at h2' ⊢
    have hk : ∀ t, ψ (e1 t) = ψ (0, t) := by
      intro t
      have : (e1 t : E0 × H) = sgc0 + (0, t) := by simp [e1, sgc0]
      rw [this, AddChar.map_add_eq_mul, hsg ψ hX, one_mul]
    simp_rw [hk]
    have e : ∑ t ∈ TT, ψ (0, t) * GPsi D ell ψ (y t) - (c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x
        = ∑ t ∈ TT, ψ (0, t) * (GPsi D ell ψ (y t) - GPsi D ell ψ x)
          + ((∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)) * GPsi D ell ψ x := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
      ring
    have hl := hK ψ hX h0
    have n1 : ‖∑ t ∈ TT, ψ (0, t) * (GPsi D ell ψ (y t) - GPsi D ell ψ x)‖ ≤ (TT.card : ℝ) * (Real.log (x + 1) + Cd + Ko) := by
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun t ht => ?_
      rw [norm_mul, AddChar.norm_apply, one_mul]
      have := move D ell hx hCd (hy t ht) hDer ψ h0
      linarith
    have n2 : ‖((∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)) * GPsi D ell ψ x‖
        ≤ ρ * (TT.card : ℝ) * (x * (Real.log x + Cd + Ko)) := by
      rw [norm_mul]
      refine mul_le_mul h2' ((triv D ell hx hCd hDer ψ h0).trans ?_) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have n3 := (norm_add_le _ _).trans (add_le_add n1 n2)
    rw [← e] at n3
    have n4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans n3)).1
    have e2 : ((c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x).re = c * TT.card * (GPsi D ell ψ x).re := by
      rw [show (c : ℂ) * (TT.card : ℂ) = ((c * TT.card : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [Complex.sub_re, e2, Complex.re_sum] at n4
    have n5 := mul_le_mul_of_nonneg_left r2 (Nat.cast_nonneg (α := ℝ) TT.card)
    nlinarith
  · unfold vv
    rw [if_neg hX, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    have k2 := h3 ψ hψ hX
    have k3 := move D ell hx hCd (hy t ht) hDer ψ h0
    have k4 : ‖GPsi D ell ψ (y t)‖ ≤ ‖GPsi D ell ψ x‖ + ‖GPsi D ell ψ (y t) - GPsi D ell ψ x‖ := by
      simpa using norm_add_le (GPsi D ell ψ x) (GPsi D ell ψ (y t) - GPsi D ell ψ x)
    have k5 : ‖ψ (e1 t) * GPsi D ell ψ (y t)‖ ≤ ‖GPsi D ell ψ x‖ + R := by
      rw [norm_mul, AddChar.norm_apply, one_mul]
      linarith
    have := (abs_le.1 ((Complex.abs_re_le_norm _).trans k5)).1
    linarith

lemma core (A0 : AddSubgroup H) (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ}
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) {x b b' η X' θ Err Y : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hS : SizesA A0 TT T2 a w N x b b' η X' θ) (hThin : ThinScales D ell X' θ)
    (hC : CostWindows x (fPl H) b η θ) (hT2 : ∀ s ∈ T2, s ∈ A0)
    (hTop : ∀ u0 ∈ A0, gapA D N ell TT a w u0 ≤ Err)
    (hY : (TT.card : ℝ) * Y ≤ ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ (a t / b)).re) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * Y ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
  classical
  obtain ⟨hη, hX', hb', hbX, hθ, ha, hwpos, hwthick, hwthin, hN⟩ := hS
  have hapos : ∀ t ∈ TT, 0 < a t := fun t ht => by
    have h1 : x - 1 ≤ a t / b := by linarith [(abs_le.1 (ha t ht)).1]
    rw [le_div_iff₀ hb] at h1
    nlinarith
  have hK : 2 * fPl H * (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) ≤ 2 * b / x := by
    have h1 := mul_le_mul_of_nonneg_left hC.1 hb.le
    have h2 := hC.2
    have e : 2 * b / x = b * (1 / x) + b / x := by ring
    rw [e]
    nlinarith
  have hu : ∀ u0 ∈ A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
    intro u0 hu0
    have h1 : ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re
        ≤ ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re + 2 * b / x) := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      have k1 := th_le D ell T2 x b b' η X' θ (a t) u0 t (w u0 j) hx hb hη hX' hb' hbX hθ (ha t ht) (hwpos u0 hu0 j)
        (hwthick u0 hu0 j) (hwthin u0 hu0 j) hThin (lipschitz_weight_all H D ell)
      have k2 := congrArg Complex.re (ch_balance D S hD ell (a t) t (w u0 j) (hapos t ht) (hwpos u0 hu0 j) N
        (fun ρ hρ => hN u0 hu0 j t ρ ht hρ))
      rw [Complex.sub_re, Complex.ofReal_re] at k2
      linarith
    simp only [Finset.sum_add_distrib] at h1
    have e : ∑ _t ∈ TT, ∑ _j : Fin m, 2 * b / x = 2 * (TT.card : ℝ) * m * b / x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    rw [e] at h1
    have := hTop u0 hu0
    unfold gapA at this
    linarith
  have hA : (0 : ℝ) < Fintype.card A0 := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u t).re
      ≤ (Fintype.card A0 : ℝ) * (Err + 2 * (TT.card : ℝ) * m * b / x) := by
    refine (Finset.sum_le_sum fun (u : A0) _ => hu u u.2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h2 : ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u t).re
      = (Fintype.card A0 : ℝ) * ((m * b * (delta2 T2 / 2)) *
        ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ (a t / b)).re) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_Th A0 D ell T2 hT2, Complex.re_ofReal_mul]
    ring
  rw [h2] at h1
  have h3 := le_of_mul_le_mul_left h1 hA
  have h4 : 0 ≤ (m : ℝ) * b * (delta2 T2 / 2) := by unfold delta2; positivity
  have h5 := mul_le_mul_of_nonneg_left hY h4
  nlinarith

end CharacterBalanceMoves

set_option maxHeartbeats 1600000 in
theorem ch_core (C ε CE Ko c M : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hc : |c| ≤ 1) : ∃ x1 : ℝ, ∀ x ≥ x1,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (D : ArithData H) (S : Finset ℕ)
      (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
      (b b' k aE η X' θ : ℝ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)),
      HostFactsS D S → 0 < b → 0 ≤ aE → 0 < k → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → x * m ≤ k →
      SizesA A0 TT T2 a w N x b b' η X' θ → ThinScales D ell X' θ → CostWindows x (fPl H) b η θ →
      RestSize ε x (Fintype.card H) TT.card T2.card m b k aE → (∀ s ∈ T2, s ∈ A0) → CharsA ell A0 Kp TT c M Ko CE ε x →
      (∀ u ∈ A0, gapA D N ell TT a w u ≤ x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) →
      GmA D ell Kp c x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell A0 Kp x := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (show 0 < 3 * ε / 8 by positivity)).eventually_ge_atTop 26)
  set A1 : ℝ := 5 + Cd + |Ko| + |M| * (4 + Cd + |Ko|) + 4 * |CE| with hA1
  have hA10 : 0 ≤ A1 := by positivity
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop (|M| * A1))
  refine ⟨max 3 (max x₁ x₂), fun x hx => ?_⟩
  intro H _ _ _ m D S ell N TT T2 a w b b' k aE η X' θ A0 Kp hHost hb ha hk hm hxm hS hThin hCost hSize hT2 hCh hTop
  obtain ⟨h0K, hKp, hM, hE2, hKo, hE3⟩ := hCh
  have hx3 : 3 ≤ x := le_of_max_le_left hx
  have h26 := hx₁ x (le_of_max_le_left (le_of_max_le_right hx))
  have hbig := hx₂ x (le_of_max_le_right (le_of_max_le_right hx))
  have hx0 : 0 < x := by linarith
  have w1 : 1 ≤ x := by linarith
  have hW : SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE
      (x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) :=
    (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, hε, hC,
      Fintype.card_pos, hb, ha, Finset.card_le_univ T2, hm, hxm⟩
  set s : ℝ := x ^ ((1 : ℝ) / 4) with hs
  set e : ℝ := x ^ ε with he
  have hs1 : 1 ≤ s := Real.one_le_rpow w1 (by norm_num)
  have he1 : 1 ≤ e := Real.one_le_rpow w1 hε.le
  have hX : x ^ ((1 : ℝ) / 2 + ε) = s * (s * e) := by
    rw [hs, he, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hρ : x ^ (-1 + ε) * x = e := by
    rw [Real.rpow_add hx0, Real.rpow_neg_one]
    field_simp
    rfl
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg w1
  have hl : Real.log x ≤ 4 * s := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hl1 : Real.log (x + 1) ≤ 5 * s := by
    have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hse : s ≤ s * e := le_mul_of_one_le_right (by linarith) he1
  have hse1 : 1 ≤ s * e := by linarith
  have up : ∀ z : ℝ, 0 ≤ z → z ≤ z * (s * e) := fun z hz => le_mul_of_one_le_right hz hse1
  have hMe : 0 ≤ |M| * (4 + Cd + |Ko|) * (s * e) := by positivity
  have hCe : 0 ≤ |CE| * (s * e) := by positivity
  have hKe : 0 ≤ |Ko| * (s * e) := by positivity
  have hCde : 0 ≤ Cd * (s * e) := by positivity
  have hR : A1 * (s * e) = 5 * (s * e) + Cd * (s * e) + |Ko| * (s * e) + |M| * (4 + Cd + |Ko|) * (s * e)
      + 4 * (|CE| * (s * e)) := by
    rw [hA1]; ring
  have hρ0 : 0 ≤ x ^ (-1 + ε) := Real.rpow_nonneg hx0.le _
  have r1 : Cd ≤ A1 * (s * e) := by linarith [up Cd hCd]
  have r2 : Real.log (x + 1) + Cd + |Ko| + |M| * x ^ (-1 + ε) * (x * (Real.log x + Cd + |Ko|)) ≤ A1 * (s * e) := by
    have e1 : |M| * x ^ (-1 + ε) * (x * (Real.log x + Cd + |Ko|)) = |M| * ((Real.log x + Cd + |Ko|) * e) := by
      rw [← hρ]; ring
    have e2 : Real.log x + Cd + |Ko| ≤ (4 + Cd + |Ko|) * s := by
      have := le_mul_of_one_le_right hCd hs1
      have := le_mul_of_one_le_right (abs_nonneg Ko) hs1
      linarith
    have e3 : |M| * ((Real.log x + Cd + |Ko|) * e) ≤ |M| * ((4 + Cd + |Ko|) * s * e) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (by linarith)) (abs_nonneg M)
    have e4 : |M| * ((4 + Cd + |Ko|) * s * e) = |M| * (4 + Cd + |Ko|) * (s * e) := by ring
    rw [e1]
    linarith [up Cd hCd, up _ (abs_nonneg Ko)]
  have r3 : Real.log (x + 1) + Cd + |CE| * Real.log x ≤ A1 * (s * e) := by
    have e1 : |CE| * Real.log x ≤ |CE| * (4 * (s * e)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg CE)
    linarith [up Cd hCd]
  have hone := CharacterBalanceMoves.one_char A0 Kp D ell TT (fun t => a t / b) (c := c) (ρ := |M| * x ^ (-1 + ε)) (Ko := |Ko|)
    (L := |CE| * Real.log x) hx3 hCd hS.2.2.2.2.2.1 (hDer H D ell) (by positivity) (abs_nonneg _) h0K
    (fun ψ h => (hKp ψ h).2)
    (fun ψ h h' => (hE2 ψ h h').trans (by gcongr; exact le_abs_self M))
    (fun ψ h h' => (hKo ψ h h').trans (le_abs_self Ko))
    (fun ψ h h1 => (hE3 ψ h h1).trans (mul_le_mul_of_nonneg_right (le_abs_self CE) hl0))
    r1 r2 r3
  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x with hG
  have hY : (TT.card : ℝ) * (G - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
      ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (CharacterBalanceMoves.e1 t) * GPsi D ell ψ (a t / b)).re := by
    simp_rw [Complex.re_sum]
    rw [Finset.sum_comm]
    refine le_trans ?_ (Finset.sum_le_sum hone)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, CharacterBalanceMoves.sum_vv A0 Kp (fun ψ h => (hKp ψ h).1), Finset.sum_const,
      nsmul_eq_mul, hX]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have k1 := mul_le_mul_of_nonneg_right (hM.trans (le_abs_self M)) (show 0 ≤ A1 * (s * e) by positivity)
    have k2 := mul_le_mul_of_nonneg_right hbig (show 0 ≤ s * e by positivity)
    have k3 : 0 ≤ s * (s * e) := by positivity
    have k4 : |M| * (A1 * (s * e)) = |M| * A1 * (s * e) := by ring
    linarith
  have hc' := CharacterBalanceMoves.core A0 D S hHost ell N TT T2 a w hx3 hb hS hThin hCost hT2 hTop hY
  have hz := proposition_size_bound _ _ _ _ _ _ _ _ _ _ _ G hW hc'
  linarith

end Deduction

end
