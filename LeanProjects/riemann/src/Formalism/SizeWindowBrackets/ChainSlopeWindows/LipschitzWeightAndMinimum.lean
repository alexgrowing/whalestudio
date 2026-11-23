import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.ChainSlopeWindows.RiemannHypothesisOfPowerBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.ThickAverageLoss.ThickAverageProofs.Balance
import Formalism.ThickAverageLoss.ThickAverageProofs.ThickAverage
import Formalism.ZetaNonvanishing.GzLipschitz
import Mathlib.NumberTheory.Chebyshev

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

namespace SZ

lemma rp {x : ℝ} (hx0 : 0 < x) (u v : ℝ) : x ^ (u + v) = x ^ u * x ^ v := Real.rpow_add hx0 u v

lemma nT_bound {x ε : ℝ} {n nT : ℝ} (hx0 : 0 < x) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) :
    n ≤ 2 * nT * x ^ (ε / 8) := by
  have h8 : 0 < x ^ (ε / 8) := Real.rpow_pos_of_pos hx0 _
  have hinv : x ^ (-(ε / 8)) * x ^ (ε / 8) = 1 := by rw [← rp hx0]; simp
  have := mul_le_mul_of_nonneg_right hnT h8.le
  have e : x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = n / 2 := by
    calc x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = (x ^ (-(ε / 8)) * x ^ (ε / 8)) * n / 2 := by ring
      _ = n / 2 := by rw [hinv]; ring
  linarith

lemma T1 {x X Y m nT aE b : ℝ} (hxX : x ≤ X * m) (hXY : X ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (haE : aE ≤ 2 * x * b) : nT * aE ≤ 2 * Y * (nT * m * b) := by
  have h1 : nT * aE ≤ nT * (2 * x * b) := mul_le_mul_of_nonneg_left haE hnT0
  have h2 : 2 * x * b ≤ 2 * (Y * m) * b := by
    have : x ≤ Y * m := le_trans hxX (mul_le_mul_of_nonneg_right hXY hm0)
    nlinarith
  have h3 : nT * (2 * x * b) ≤ nT * (2 * (Y * m) * b) := mul_le_mul_of_nonneg_left h2 hnT0
  calc nT * aE ≤ nT * (2 * (Y * m) * b) := le_trans h1 h3
    _ = 2 * Y * (nT * m * b) := by ring

lemma T2 {x Y m nT aE b k : ℝ} (hx0 : 0 < x) (hY1 : 1 ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hk0 : 0 < k) (hk1 : x * m ≤ k) (haE : aE ≤ 2 * x * b) :
    nT * aE * (m ^ 2 / k) ≤ 2 * Y * (nT * m * b) := by
  have hmk : m ^ 2 / k ≤ m / x := by
    rw [div_le_div_iff₀ hk0 hx0]; nlinarith
  have h1 : nT * aE * (m ^ 2 / k) ≤ nT * (2 * x * b) * (m / x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haE hnT0) hmk (by positivity) (by positivity)
  have h2 : nT * (2 * x * b) * (m / x) = 2 * (nT * m * b) := by field_simp
  have hQ : 0 ≤ nT * m * b := by positivity
  have h3 : 2 * (nT * m * b) ≤ 2 * Y * (nT * m * b) := by nlinarith
  linarith

lemma T3 {x ε Y m n nT b : ℝ} (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hY' : x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) = Y := by
    rw [← rp hx0, ← rp hx0, hY]; ring_nf
  have hmY : m * x ^ ε * x ^ (ε / 8) ≤ Y := by
    rw [← hY']; gcongr
  have hnT' := nT_bound hx0 hnT
  have key : 2 * n * m * x ^ ε ≤ 4 * Y * nT := by
    have hme : 0 ≤ m * x ^ ε := by positivity
    have hnT0 : 0 ≤ nT := by nlinarith
    calc 2 * n * m * x ^ ε = 2 * n * (m * x ^ ε) := by ring
      _ ≤ 2 * (2 * nT * x ^ (ε / 8)) * (m * x ^ ε) := by gcongr
      _ = 4 * nT * (m * x ^ ε * x ^ (ε / 8)) := by ring
      _ ≤ 4 * nT * Y := by gcongr
      _ = 4 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc m * ((2 * n) * m * b * x ^ ε) = (2 * n * m * x ^ ε) * (m * b) := by ring
    _ ≤ (4 * Y * nT) * (m * b) := mul_le_mul_of_nonneg_right key hmb
    _ = 4 * Y * (nT * m * b) := by ring

lemma T4 {x ε Y m n nT nT2 b k : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m) (hb : 0 ≤ b) (hε : 0 < ε)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 < n)
    (hnT2 : nT2 ≤ n) (hk0 : 0 ≤ k) (hk2 : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) :
    m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) ≤ 2 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have pne := Real.rpow_pos_of_pos hx0 (-ε)
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hneg : x ^ (-ε) * x ^ ε = 1 := by rw [← rp hx0]; simp
  have he : m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
      = (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) := by
    have h2 : x ^ ε = 1 / x ^ (-ε) := by rw [eq_div_iff pne.ne', mul_comm, hneg]
    rw [h2]; field_simp
  rw [he]
  have hA : nT2 * k * (x ^ ε * x ^ ε) / n ^ 2 ≤ n * x ^ ((1 : ℝ) / 2 + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have hxe : 0 ≤ x ^ ε * x ^ ε := by positivity
    have e2 : n * x ^ ((1 : ℝ) / 2 + ε) * n ^ 2 = n * (n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) * (x ^ ε * x ^ ε) := by
      rw [show (1 : ℝ) / 2 + ε = ((1 : ℝ) / 2 - ε) + ε + ε by ring, rp hx0, rp hx0]; ring
    rw [e2]
    have := mul_le_mul hnT2 hk2 hk0 hn.le
    exact mul_le_mul_of_nonneg_right this hxe
  have hnT' := nT_bound hx0 hnT
  have hXe : x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8) ≤ Y := by
    rw [← rp hx0, hY]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hB : n * x ^ ((1 : ℝ) / 2 + ε) ≤ 2 * Y * nT := by
    have hp := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 + ε)
    have hnT0 : 0 ≤ nT := by nlinarith
    calc n * x ^ ((1 : ℝ) / 2 + ε) ≤ (2 * nT * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε) :=
          mul_le_mul_of_nonneg_right hnT' hp.le
      _ = 2 * nT * (x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8)) := by ring
      _ ≤ 2 * nT * Y := by gcongr
      _ = 2 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) ≤ (m * b) * (n * x ^ ((1 : ℝ) / 2 + ε)) :=
        mul_le_mul_of_nonneg_left hA hmb
    _ ≤ (m * b) * (2 * Y * nT) := mul_le_mul_of_nonneg_left hB hmb
    _ = 2 * Y * (nT * m * b) := by ring

end SZ

namespace CR

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma primVal_zero (D : ArithData H) (n : ℕ) : primVal D 0 n = 1 := by
  classical
  unfold primVal
  apply Finset.prod_eq_one
  intro p _
  unfold cosetMean
  simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  apply div_self
  have h0 : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ D.inertia p) := by
    simp
  have := Finset.card_pos.2 ⟨0, h0⟩
  exact_mod_cast this.ne'

lemma chC_apply' (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.1 : ℝ) : ℂ) := by
  show (if g.1.1 = 0 then (1 : ℂ) else -1) = _
  unfold sgn2; split_ifs <;> simp

lemma psC_apply' (g : E0 × H) : (psC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.2 : ℝ) : ℂ) := by
  show (if g.1.2 = 0 then (1 : ℂ) else -1) = _
  unfold sgn2; split_ifs <;> simp

lemma chpsC_apply' (g : E0 × H) :
    (chpsC : AddChar (E0 × H) ℂ) g = ((sgn2 g.1.1 * sgn2 g.1.2 : ℝ) : ℂ) := by
  unfold chpsC; rw [AddChar.mul_apply, chC_apply', psC_apply']; push_cast; ring

def host (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : CycHost H where
  cv := primVal D
  cv_zero := primVal_zero D
  ell := ell
  chC := chC
  psC := psC
  chpsC := chpsC
  chC_apply := chC_apply'
  psC_apply := psC_apply'
  chpsC_apply := chpsC_apply'

lemma GC_host (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (y : ℝ) :
    GC (host D ell) ψ y = GPsi D ell ψ y := rfl

lemma De_re (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    (De D ell a t w).re = balTop (host D ell) a t w := by
  unfold De balTop
  have hf : univ.filter (fun g : E0 × H => ¬ InPhi g) = univ.filter (fun g => ¬ InPhi (g + topPl t)) := by
    ext g; simp [Formalism.D5.Bal.inPhi_add_topPl]
  rw [hf]
  refine congrArg Complex.re (congrArg _ (Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun ψ _ => ?_))
  rw [AddChar.map_neg_eq_conj]; rfl

lemma card_char : (Fintype.card (AddChar (E0 × H) ℂ) : ℝ) = 2 * fPl H := by
  rw [AddChar.card_eq]
  have := Formalism.D5.Bal.card_G_eq (H := H)
  unfold fPl
  exact_mod_cast this

lemma fPl_pos : 0 < fPl H := by
  unfold fPl
  have := Formalism.D5.Bal.phiSet_card_ne_zero (H := H)
  have h : (PhiSet (H := H)).card ≠ 0 := by exact_mod_cast this
  exact_mod_cast Nat.pos_of_ne_zero h

lemma card_S_le (t : H) (S : Finset (E0 × H)) (hS : S ⊆ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))) :
    (S.card : ℝ) ≤ fPl H := by
  have := Finset.card_le_card hS
  rw [Formalism.D5.Bal.card_S t] at this
  unfold fPl; exact_mod_cast this

lemma norm_avg_le (S : Finset (E0 × H)) (hS : (S.card : ℝ) ≤ fPl H) (F : E0 × H → AddChar (E0 × H) ℂ → ℂ)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ g ∈ S, ∀ ψ, ‖F g ψ‖ ≤ K) :
    ‖(1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖
      ≤ 2 * fPl H * K := by
  have hf := fPl_pos (H := H)
  rw [norm_mul]
  have h1 : ‖(1 / ((PhiSet (H := H)).card : ℂ))‖ = 1 / fPl H := by
    unfold fPl; rw [norm_div, norm_one]; simp
  rw [h1]
  have h2 : ‖∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖ ≤ (S.card : ℝ) * (2 * fPl H) * K := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ g ∈ S, ‖∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖ ≤ (2 * fPl H) * K := by
      intro g hg
      refine le_trans (norm_sum_le _ _) ?_
      have : ∀ ψ ∈ (univ : Finset (AddChar (E0 × H) ℂ)), ‖ψ (-g) * F g ψ‖ ≤ K := by
        intro ψ _; rw [norm_mul, AddChar.norm_apply, one_mul]; exact hK g hg ψ
      refine le_trans (Finset.sum_le_sum this) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_char]
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [Finset.sum_const, nsmul_eq_mul]; ring_nf; rfl
  calc 1 / fPl H * ‖∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖
      ≤ 1 / fPl H * ((S.card : ℝ) * (2 * fPl H) * K) := by gcongr
    _ ≤ 1 / fPl H * (fPl H * (2 * fPl H) * K) := by
        gcongr
    _ = 2 * fPl H * K := by field_simp

lemma partner_inPhi {g : E0 × H} (t : H) (hg : ¬ InPhi (g + topPl t)) : InPhi (cconj + g + topPl t) := by
  rw [Formalism.D5.Bal.inPhi_add_topPl] at hg
  have h1 : g.1.1 = 1 := (Formalism.D5.Bal.zmod_two_ne_zero_iff_eq_one _).1 hg
  show (cconj + g + topPl t).1.1 = 0
  simp [cconj, topPl, h1]
  decide

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma mean_le {m : ℕ} (TT : Finset H) (F G : H → H → Fin m → ℝ) (K : ℝ)
    (h : ∀ u0, ∀ t ∈ TT, ∀ j, F u0 t j ≤ G u0 t j + K) :
    (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ (1 / (Fintype.card H : ℝ)) * (∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j) + (TT.card : ℝ) * m * K := by
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, (G u0 t j + K) :=
    Finset.sum_le_sum fun u0 _ => Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => h u0 t ht j
  have h2 : ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, (G u0 t j + K)
      = (∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j) + (Fintype.card H : ℝ) * ((TT.card : ℝ) * m * K) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  calc (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ (1 / (Fintype.card H : ℝ)) * ((∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j)
          + (Fintype.card H : ℝ) * ((TT.card : ℝ) * m * K)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

lemma psC_ne_zero : (psC : AddChar (E0 × H) ℂ) ≠ 0 := by
  intro h
  have := congrArg (fun χ : AddChar (E0 × H) ℂ => χ ((0, 1), 0)) h
  simp only [AddChar.zero_apply, psC_apply'] at this
  norm_num [sgn2] at this

lemma chC_ne_zero : (chC : AddChar (E0 × H) ℂ) ≠ 0 := by
  intro h
  have := congrArg (fun χ : AddChar (E0 × H) ℂ => χ ((1, 0), 0)) h
  simp only [AddChar.zero_apply, chC_apply'] at this
  norm_num [sgn2] at this

lemma chpsC_ne_zero : (chpsC : AddChar (E0 × H) ℂ) ≠ 0 := by
  intro h
  have := congrArg (fun χ : AddChar (E0 × H) ℂ => χ ((1, 0), 0)) h
  simp only [AddChar.zero_apply, chpsC_apply'] at this
  norm_num [sgn2] at this

lemma three_bound (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x ε Cd CL y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (hVal : ValuesAtX D ell x ε CL)
    (ψ : AddChar (E0 × H) ℂ) (hψ : ψ = psC ∨ ψ = chC ∨ ψ = chpsC) :
    ‖GPsi D ell ψ y‖ ≤ x ^ ((1 : ℝ) / 2 + ε) + (Real.log (x + 1) + Cd + CL * Real.log x) := by
  have hψ0 : ψ ≠ 0 := by
    rcases hψ with rfl | rfl | rfl
    · exact psC_ne_zero
    · exact chC_ne_zero
    · exact chpsC_ne_zero
  obtain ⟨hv, hl⟩ := hVal ψ hψ
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hd := hDer.1 ψ hψ0 y x (by linarith) (by linarith)
  have hmax : max y x ≤ x + 1 := max_le (by linarith) (by linarith)
  have hmax1 : 1 ≤ max y x := le_trans (by linarith) (le_max_right y x)
  have hlog : Real.log (max y x) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hmax
  have hlog0 : 0 ≤ Real.log (max y x) := Real.log_nonneg hmax1
  have hs : 0 ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by positivity
  have h1 : |y - x| * (Real.log (max y x) + Cd + ‖ell ψ‖) ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by
    calc |y - x| * (Real.log (max y x) + Cd + ‖ell ψ‖) ≤ 1 * (Real.log (max y x) + Cd + ‖ell ψ‖) :=
          mul_le_mul_of_nonneg_right hy hs
      _ = _ := one_mul _
  have h2 : ‖GPsi D ell ψ y‖ ≤ ‖GPsi D ell ψ x‖ + ‖GPsi D ell ψ y - GPsi D ell ψ x‖ := by
    have := norm_add_le (GPsi D ell ψ x) (GPsi D ell ψ y - GPsi D ell ψ x)
    simpa using this
  linarith

lemma signal_term (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x ε Cd CL y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (hVal : ValuesAtX D ell x ε CL) :
    Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL
      ≤ (GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y).re := by
  have h0 : (GPsi D ell 0 y).re = Gz y := by simp [GPsi]
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hG := hDer.2 y x (by linarith) (by linarith)
  have hG' : |Gz y - Gz x| ≤ Cd := by
    calc |Gz y - Gz x| ≤ Cd * |y - x| := hG
      _ ≤ Cd * 1 := mul_le_mul_of_nonneg_left hy hCd
      _ = Cd := mul_one _
  have hGl := (abs_le.1 hG').1
  have b1 := three_bound D ell hx hCd hy hDer hVal psC (Or.inl rfl)
  have b2 := three_bound D ell hx hCd hy hDer hVal chC (Or.inr (Or.inl rfl))
  have b3 := three_bound D ell hx hCd hy hDer hVal chpsC (Or.inr (Or.inr rfl))
  have r1 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b1)).1
  have r2 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b2)).2
  have r3 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b3)).2
  simp only [Complex.add_re, Complex.sub_re, h0]
  unfold moveCost
  linarith

lemma balTop_diff (Hs : CycHost H) (a : ℝ) (t : H) (w w' : E0 × H → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ g, ¬ InPhi (g + topPl t) → ∀ ψ : AddChar (E0 × H) ℂ,
      ‖((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
        - ((w' (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w' (cconj + g + topPl t))‖ ≤ K) :
    |balTop Hs a t w - balTop Hs a t w'| ≤ 2 * fPl H * K := by
  have e : balTop Hs a t w - balTop Hs a t w'
      = ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
          ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) *
            (((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
              - ((w' (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w' (cconj + g + topPl t)))).re := by
    unfold balTop
    rw [← Complex.sub_re, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg Complex.re (congrArg _ (Finset.sum_congr rfl fun g _ => ?_))
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  rw [e]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  apply norm_avg_le _ (card_S_le t _ (Finset.Subset.refl _)) _ K hK0
  intro g hg ψ
  exact hK g (Finset.mem_filter.1 hg).2 ψ

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def wR {m : ℕ} (T2 : Finset H) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) : H → Fin m → E0 × H → ℝ :=
  fun u0 j ρ => if IsThickAt T2 u0 ρ then b else if InPhi ρ then w u0 j ρ else 1

def aR (TT : Finset H) (a : H → ℝ) : H → ℝ := fun t => if t ∈ TT then a t else 1

lemma wR_thick {m : ℕ} (T2 : Finset H) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) (u0 : H) (j : Fin m) (ρ : E0 × H)
    (h : IsThickAt T2 u0 ρ) : wR T2 b w u0 j ρ = b := by unfold wR; rw [if_pos h]

lemma wR_thin {m : ℕ} (T2 : Finset H) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) (u0 : H) (j : Fin m) (ρ : E0 × H)
    (h : ¬ IsThickAt T2 u0 ρ) (hρ : InPhi ρ) : wR T2 b w u0 j ρ = w u0 j ρ := by
  unfold wR; rw [if_neg h, if_pos hρ]

lemma aR_mem (TT : Finset H) (a : H → ℝ) {t : H} (ht : t ∈ TT) : aR TT a t = a t := by
  unfold aR; rw [if_pos ht]

def nodes {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (b : ℝ) (w : H → Fin m → E0 × H → ℝ) (hb : 0 < b)
    (ha : ∀ t ∈ TT, 0 < a t) (hw : ∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) : Nodes H m where
  T := TT
  T2 := T2
  a := aR TT a
  bj := fun _ => b
  w := wR T2 b w
  w_thick := fun u0 j t ht => wR_thick T2 b w u0 j _ (Finset.mem_image_of_mem _ ht)
  w_pos := fun u0 j ρ => by
    unfold wR; split_ifs with h1 h2
    · exact hb
    · exact hw u0 j ρ h2
    · exact one_pos
  a_pos := fun t => by
    unfold aR; split_ifs with h
    · exact ha t h
    · exact one_pos

end

end CR

theorem proposition_finite_group {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : GrowthInequalityExplicit (H := H) := by
  intro hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hx, hb, hη, hX', hb', hbX, hθ, hCd, ha, ⟨hwpos, hwthick, hwthin⟩, hN, hTop, hThin, hLip, hDer, hVal⟩ := hH
  have haB : ∀ t ∈ TT, (x - 1) * b ≤ a t ∧ a t ≤ (x + 1) * b := by
    intro t ht
    obtain ⟨h1, h2⟩ := abs_le.1 (ha t ht)
    constructor
    · have : x - 1 ≤ a t / b := by linarith
      rwa [le_div_iff₀ hb] at this
    · have : a t / b ≤ x + 1 := by linarith
      rwa [div_le_iff₀ hb] at this
  have hapos : ∀ t ∈ TT, 0 < a t := fun t ht => lt_of_lt_of_le (by nlinarith) (haB t ht).1
  have hf := CR.fPl_pos (H := H)

  have hA : topExcess D N ell TT a w = (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (a t) t (w u0 j) := by
    unfold topExcess
    refine congrArg _ (Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun t ht =>
      Finset.sum_congr rfl fun j _ => ?_)
    have h1 := hBal D hD ell (a t) t (w u0 j) (hapos t ht) (hwpos u0 j) N (fun ρ hρ => hN u0 j t ρ ht hρ)
    have h2 := congrArg Complex.re h1
    rw [Complex.sub_re, Complex.ofReal_re, CR.De_re] at h2
    exact h2

  have hB : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
        ≤ balTop (CR.host D ell) (a t) t (w u0 j) + 2 * fPl H * (3 * (x + 1) * (η + 1)) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hd := CR.balTop_diff (CR.host D ell) (a t) t (w u0 j) (CR.wR T2 b w u0 j) (3 * (x + 1) * (η + 1))
      (by positivity) (by
        intro g hg ψ
        have hρ := CR.partner_inPhi t hg
        by_cases hth : IsThickAt T2 u0 (cconj + g + topPl t)
        · rw [CR.wR_thick T2 b w u0 j _ hth]
          obtain ⟨h1, h2⟩ := hwthick u0 j _ hth
          have hl := hLip ψ (a t) (w u0 j (cconj + g + topPl t)) b (hapos t ht) (hwpos u0 j _ hρ) hb
          rw [min_eq_right h1, abs_of_nonneg (by linarith)] at hl
          refine le_trans hl ?_
          have e1 : 3 * a t / b ≤ 3 * (x + 1) := by
            rw [div_le_iff₀ hb]; nlinarith [(haB t ht).2]
          have e0 : 0 ≤ 3 * a t / b := by have := hapos t ht; positivity
          exact mul_le_mul e1 (by linarith) (by linarith) (by positivity)
        · rw [CR.wR_thin T2 b w u0 j _ hth hρ, sub_self, norm_zero]; positivity)
    have := (abs_le.1 hd).1
    linarith
  have hB' := CR.mean_le TT (fun u0 t j => balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j))
    (fun u0 t j => balTop (CR.host D ell) (a t) t (w u0 j)) _ hB

  have hTA := thick_average_formula (H := H) (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)

  have hC : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m, (0 : ℝ) ≤
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
        + 2 * fPl H * ((x + 1) * b * θ) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hn := CR.norm_avg_le (univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)))
      (CR.card_S_le t _ (by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        exact ⟨hg.1, hg.2.1⟩))
      (fun g ψ => ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (a t / CR.wR T2 b w u0 j (cconj + g + topPl t)))
      ((x + 1) * b * θ) (by positivity) (by
        intro g hg ψ
        obtain ⟨hg1, hg2⟩ := (Finset.mem_filter.1 hg).2
        have hρ := CR.partner_inPhi t hg1
        rw [CR.wR_thin T2 b w u0 j _ hg2 hρ]
        have hw0 := hwpos u0 j _ hρ
        have hw2 := hwthin u0 j _ hρ hg2
        have hy : X' / 3 ≤ a t / w u0 j (cconj + g + topPl t) := by
          rw [le_div_iff₀ hw0]
          have h1 : X' / 3 * w u0 j (cconj + g + topPl t) ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          have h2 := (haB t ht).1
          nlinarith
        have ht' := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        calc w u0 j (cconj + g + topPl t) * ‖GC (CR.host D ell) ψ (a t / w u0 j (cconj + g + topPl t))‖
            ≤ w u0 j (cconj + g + topPl t) * (a t / w u0 j (cconj + g + topPl t) * θ) :=
              mul_le_mul_of_nonneg_left ht' hw0.le
          _ = a t * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right (haB t ht).2 hθ)
    have hre := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) hn)).1
    simp only [mul_assoc] at hre ⊢
    linarith
  have hC' := CR.mean_le TT (fun _ _ _ => (0 : ℝ)) _ _ hC
  have hrest : -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ)))
      ≤ restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    simp only [Finset.sum_const_zero, mul_zero] at hC'
    have : restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) = _ := rfl
    unfold restAvg
    show -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))) ≤ (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
    linarith

  have hD' : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    show _ ≤ ((T2.card : ℝ) / Fintype.card H) / 2 * ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re
    have hs : ∑ t ∈ TT, ∑ _j : Fin m, b * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
        ≤ ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      rw [CR.aR_mem TT a ht]
      exact mul_le_mul_of_nonneg_left (CR.signal_term D ell hx hCd (ha t ht) hDer hVal) hb.le
    have hδ : 0 ≤ ((T2.card : ℝ) / Fintype.card H) / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hs hδ
    refine le_trans (le_of_eq ?_) this
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    unfold delta2; ring

  have hTA' : (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
      = signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)
        + restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := hTA
  rw [← hA, hTA'] at hB'
  have e1 : (TT.card : ℝ) * m * (2 * fPl H * (3 * (x + 1) * (η + 1)))
      = (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) := by ring
  have e2 : (TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))
      = (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) := by ring
  rw [e1] at hB'
  rw [e2] at hrest
  linarith

theorem proposition_size_bound : GrowthSizeBound := by
  intro C ε x n nT nT2 m b k aE Err Gx hW hT
  obtain ⟨hx3, hε, hC, hn, hb, haE0, haE, hnT, hd2, hnT2, hm1, hm2, hk1, hk2, hErr, hbig⟩ := hW
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have pos : ∀ u : ℝ, 0 < x ^ u := fun u => Real.rpow_pos_of_pos hx0 u
  have mono : ∀ u v : ℝ, u ≤ v → x ^ u ≤ x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hP1 : 1 ≤ x ^ (C * ε) := Real.one_le_rpow hx1 (by positivity)
  have hY1 : 1 ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := Real.one_le_rpow hx1 (by linarith)
  have hXY : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := mono _ _ (by linarith)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (pos _) hm1
  have hnT0 : (0 : ℝ) < nT := lt_of_lt_of_le (by have := pos (-(ε / 8)); positivity) hnT
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
  have hQ : 0 < (nT : ℝ) * m * b := by positivity
  have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m := by
    have e : x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) = x := by
      rw [← SZ.rp hx0]; norm_num
    calc x = x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) := e.symm
      _ ≤ x ^ ((1 : ℝ) / 2 + ε) * m := mul_le_mul_of_nonneg_left hm1 (pos _).le
  have h1 := SZ.T1 hxX hXY hnT0.le hm0.le hb.le haE
  have h2 := SZ.T2 hx0 hY1 hnT0.le hm0.le hb.le hk0 hk1 haE
  have h3 := SZ.T3 (ε := ε) (n := (n : ℝ)) hx0 hm0.le hb.le rfl hm2 hnT hnR.le
  have h4 := SZ.T4 (nT2 := (nT2 : ℝ)) hx0 hx1 hm0.le hb.le hε rfl hnT hnR (by exact_mod_cast hnT2) hk0.le hk2
  have hErr' : Err ≤ 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
    refine le_trans hErr ?_
    have hsum : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
        ≤ 10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
      have e : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
          + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
          = (nT : ℝ) * aE + (nT : ℝ) * aE * ((m : ℝ) ^ 2 / k) + (m : ℝ) * ((2 * n) * m * b * x ^ ε)
            + (m : ℝ) * ((nT2 : ℝ) * k * b * x ^ ε / (n * (n * x ^ (-ε)))) := by ring
      rw [e]; linarith
    have hP0 : 0 ≤ x ^ (C * ε) := (pos _).le
    calc x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))))
        ≤ x ^ (C * ε) * (10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b)) :=
          mul_le_mul_of_nonneg_left hsum hP0
      _ = 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by ring
  generalize hPd : x ^ (C * ε) = P at hErr' hP1
  generalize hYd : x ^ ((1 : ℝ) / 2 + 13 * ε / 8) = Y at hErr' hY1 hXY
  generalize hXd : x ^ ((1 : ℝ) / 2 + ε) = X at hT hXY
  generalize hQd : (nT : ℝ) * m * b = Q at hErr' hQ
  have hT' : Q * ((nT2 : ℝ) / n / 2) * (Gx - 4 * X) ≤ Err + 2 * Q / x := by
    rw [← hQd]; simpa [mul_assoc] using hT
  generalize hδd : ((nT2 : ℝ) / n) = δ at hT' hd2
  have hδ0 : 0 < δ := lt_of_lt_of_le (pos _) hd2
  have hxδ : 1 ≤ x ^ ε * δ := by
    have := mul_le_mul_of_nonneg_left hd2 (pos ε).le
    have e : x ^ ε * x ^ (-ε) = 1 := by rw [← SZ.rp hx0]; simp
    linarith
  have h2x : 2 / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hPY : 1 ≤ P * Y := by nlinarith
  have hmain : δ * (Gx - 4 * X) ≤ 22 * (P * Y) := by
    have h1 : Q * (δ / 2 * (Gx - 4 * X)) ≤ Q * (10 * P * Y + 2 / x) := by
      have e1 : Q * (δ / 2 * (Gx - 4 * X)) = Q * (δ / 2) * (Gx - 4 * X) := by ring
      have e2 : Q * (10 * P * Y + 2 / x) = 10 * P * Y * Q + 2 * Q / x := by ring
      rw [e1, e2]; linarith
    have h2 := le_of_mul_le_mul_left h1 hQ
    have e3 : δ * (Gx - 4 * X) = 2 * (δ / 2 * (Gx - 4 * X)) := by ring
    have e4 : 10 * P * Y = 10 * (P * Y) := by ring
    rw [e3]; rw [e4] at h2; linarith
  have hG : Gx - 4 * X ≤ 22 * (P * Y) * x ^ ε := by
    by_cases hc : Gx - 4 * X ≤ 0
    · have : 0 ≤ 22 * (P * Y) * x ^ ε := by have := pos ε; positivity
      linarith
    · have hc' : 0 < Gx - 4 * X := lt_of_not_ge hc
      have hxe := pos ε
      calc Gx - 4 * X ≤ (x ^ ε * δ) * (Gx - 4 * X) := le_mul_of_one_le_left hc'.le hxδ
        _ = x ^ ε * (δ * (Gx - 4 * X)) := by ring
        _ ≤ x ^ ε * (22 * (P * Y)) := mul_le_mul_of_nonneg_left hmain hxe.le
        _ = 22 * (P * Y) * x ^ ε := by ring
  have hZ : P * Y * x ^ ε = x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hPd, ← hYd, ← SZ.rp hx0, ← SZ.rp hx0]; ring_nf
  have hXZ : X ≤ x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hXd]; exact mono _ _ (by have := mul_nonneg hC hε.le; linarith)
  have hfin : x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) = x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
    rw [← SZ.rp hx0]; ring_nf
  have hZ0 := pos ((1 : ℝ) / 2 + (C + 21 / 8) * ε)
  have hG26 : Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    have : 22 * (P * Y) * x ^ ε = 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by rw [mul_assoc, hZ]
    linarith
  rw [← hfin]
  calc Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := hG26
    _ ≤ x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := mul_le_mul_of_nonneg_right hbig hZ0.le

theorem growthInequality {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : GrowthInequalityForm (H := H) := by
  intro hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH hS
  have hc := proposition_finite_group hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hMv, hth, hlip⟩ := hS
  have hx : 3 ≤ x := hH.1
  have hb : 0 < b := hH.2.1
  have hK : 0 ≤ (TT.card : ℝ) * m := by positivity
  have hδ : 0 ≤ delta2 T2 / 2 := by unfold delta2; positivity
  have h1 : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) ≤ (TT.card : ℝ) * m * (b * (1 / x)) := by
    apply mul_le_mul_of_nonneg_left _ hK
    calc 2 * fPl H * (x + 1) * b * θ = b * (2 * fPl H * (x + 1) * θ) := by ring
      _ ≤ b * (1 / x) := mul_le_mul_of_nonneg_left hth hb.le
  have h3 : (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) ≤ (TT.card : ℝ) * m * (b / x) :=
    mul_le_mul_of_nonneg_left hlip hK
  have e : 2 * (TT.card : ℝ) * m * b / x = (TT.card : ℝ) * m * (b * (1 / x)) + (TT.card : ℝ) * m * (b / x) := by
    ring
  rw [e]; linarith

theorem proposition_joint : RiemannHypothesisOfBalanceAndGrowthData := by
  intro hBal C ε₁ hε₁ hIn
  apply Formalism.LFunctionChainParameters.ConditionalMainTheorem.riemann_hypothesis_of_power_bound (C + 3) ε₁ hε₁
  intro ε hε hεl
  obtain ⟨x₀, hx₀⟩ := hIn ε hε hεl
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD, hH, hS, hW⟩ := hx₀ x hx
  have ht := growthInequality (hBal H) D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH hS
  exact proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE Err (Gz x) hW ht

theorem top_from_weighted_mean {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : LeadingTermTranslateMean (H := H) := by
  intro W _ _ Top _ m f Dd D N ell TT a w eT eP E haT hw hgam hLpL hASK hle
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hfc : f = (PhiSet (H := H)).card := by
    have := Fintype.card_congr eP
    simpa using this
  have hMain : ∀ u0, Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w u0 j)).re := by
    intro u0
    unfold Formalism.RankGapBounds.WeightedMeanData.Data.Main
    rw [Finset.sum_comm]
    have hre : ∀ (t : H) (j : Fin m), (MAIN ell (a t) (w u0 j)).re
        = a t * (Real.log (a t) - 1 - Real.eulerMascheroniConstant + (ell chC).re
          - (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ ∈ PhiSet (H := H), Real.log (w u0 j ρ)) := by
      intro t j
      unfold MAIN
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    simp only [hre]
    rw [← Finset.sum_coe_sort TT, ← Equiv.sum_comp eT]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    have hfR : (f : ℝ) = ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast hfc
    have hsum : ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ) = ∑ ρ ∈ PhiSet (H := H), Real.log (w u0 j ρ) := by
      rw [← Finset.sum_coe_sort (PhiSet (H := H)), ← Equiv.sum_comp eP]
      exact Finset.sum_congr rfl fun ρ _ => by rw [hw]
    rw [haT, hgam, hLpL, hfR, hsum]
  unfold topExcess
  unfold Formalism.RankGapBounds.WeightedMeanData.umean at hle
  simp only [hASK, hMain] at hle
  simp only [Finset.sum_sub_distrib]
  rw [mul_sub, one_div, inv_mul_eq_div, inv_mul_eq_div]
  linarith

theorem proposition_at_point : GrowthBoundAtPoint := by
  intro C ε x hI
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD, hH, hS, hW⟩ := hI
  have ht := growthInequality (Formalism.LFunctionChainParameters.characterSumData.colour_balance (H := H)) D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL
    Err hH hS
  exact proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE Err (Gz x) hW ht

theorem proposition_final : GrowthBoundGivesRiemannHypothesis :=
  proposition_joint (fun H _ _ _ => Formalism.LFunctionChainParameters.characterSumData.colour_balance (H := H))

namespace AN

lemma psi_le_three {y : ℝ} (hy : 0 ≤ y) : Chebyshev.psi y ≤ 3 * y := by
  by_cases h1 : y < 1
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]; linarith
  · have h1' : 1 ≤ y := not_lt.1 h1
    have hp := Chebyshev.psi_le h1'
    have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 (by linarith)
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
    have hlog : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [← hss, Real.log_mul hs0.ne' hs0.ne', hss]; ring
    have hu : Real.log (Real.sqrt y) ≤ Real.sqrt y * Real.exp (-1) := by
      have := Real.add_one_le_exp (Real.log (Real.sqrt y) - 1)
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hs0] at this
      linarith
    have he := Real.exp_neg_one_lt_d9
    have hl2 := Real.log_two_lt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h2 : 2 * Real.sqrt y * Real.log y ≤ 4 * Real.exp (-1) * y := by
      rw [hlog]
      have : Real.sqrt y * Real.log (Real.sqrt y) ≤ Real.sqrt y * (Real.sqrt y * Real.exp (-1)) :=
        mul_le_mul_of_nonneg_left hu hs0.le
      nlinarith
    nlinarith

lemma sum_vM_le {Y : ℝ} (hY : 0 ≤ Y) : ∑ n ∈ Icc 1 ⌊Y⌋₊, Λ n ≤ 3 * Y := by
  rw [Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc]; exact psi_le_three hY

lemma truncC (c : ℕ → ℂ) (y : ℝ) (M : ℕ) (hM : ⌊y⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, c n * ((y / n - 1 : ℝ) : ℂ) = ∑ n ∈ Icc 1 M, c n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  have h1 : ∑ n ∈ Icc 1 ⌊y⌋₊, c n * ((max (y / n - 1) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 M, c n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hM)
    intro n hn hn'
    rw [Finset.mem_Icc] at hn hn'
    have hlt : ⌊y⌋₊ < n := by
      by_contra h; exact hn' ⟨hn.1, not_lt.1 h⟩
    have hy : y < n := (Nat.floor_lt' (by omega)).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : y / n - 1 ≤ 0 := by
      have := (div_lt_one hn0).2 hy; linarith
    rw [max_eq_right this]; simp
  rw [← h1]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hy : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).1 hn.2
  have : 0 ≤ y / n - 1 := by
    have := (one_le_div hn0).2 hy; linarith
  rw [max_eq_left this]

lemma truncR (c : ℕ → ℝ) (y : ℝ) (M : ℕ) (hM : ⌊y⌋₊ ≤ M) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, c n * (y / n - 1) = ∑ n ∈ Icc 1 M, c n * (max (y / n - 1) 0) := by
  have h1 : ∑ n ∈ Icc 1 ⌊y⌋₊, c n * (max (y / n - 1) 0) = ∑ n ∈ Icc 1 M, c n * (max (y / n - 1) 0) := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hM)
    intro n hn hn'
    rw [Finset.mem_Icc] at hn hn'
    have hlt : ⌊y⌋₊ < n := by
      by_contra h; exact hn' ⟨hn.1, not_lt.1 h⟩
    have hy : y < n := (Nat.floor_lt' (by omega)).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : y / n - 1 ≤ 0 := by
      have := (div_lt_one hn0).2 hy; linarith
    rw [max_eq_right this]; simp
  rw [← h1]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hy : (n : ℝ) ≤ y := (Nat.le_floor_iff' (by omega)).1 hn.2
  have : 0 ≤ y / n - 1 := by
    have := (one_le_div hn0).2 hy; linarith
  rw [max_eq_left this]

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma norm_cosetMean_le (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ) :
    ‖cosetMean I h ψ‖ ≤ 1 := by
  classical
  unfold cosetMean
  rw [norm_div]
  have hc : (0 : ℝ) < ((univ.filter (fun x => x ∈ I)).card : ℝ) := by
    have h0 : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ I) := by simp
    exact_mod_cast Finset.card_pos.2 ⟨0, h0⟩
  have hn : ‖(((univ.filter (fun x => x ∈ I)).card : ℕ) : ℂ)‖ = ((univ.filter (fun x => x ∈ I)).card : ℝ) := by
    simp
  rw [hn, div_le_one hc]
  refine le_trans (norm_sum_le _ _) ?_
  simp [AddChar.norm_apply]

lemma norm_primVal_le (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (n : ℕ) : ‖primVal D ψ n‖ ≤ 1 := by
  unfold primVal
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun p _ => norm_cosetMean_le _ _ _)

lemma norm_coef_le (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (n : ℕ) :
    ‖(Λ n : ℂ) * primVal D ψ n‖ ≤ Λ n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (norm_primVal_le D ψ n)

end

end AN

namespace AN

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma deriv_char (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (y z : ℝ) (hy : 1 ≤ y) (_hz : 1 ≤ z) :
    ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖ell ψ‖) := by
  have hyM : ⌊y⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_left _ _)
  have hzM : ⌊z⌋₊ ≤ ⌊max y z⌋₊ := Nat.floor_le_floor (le_max_right _ _)
  have hmax1 : 1 ≤ max y z := le_trans hy (le_max_left _ _)
  have hM1 : 1 ≤ ⌊max y z⌋₊ := Nat.le_floor (by simpa using hmax1)
  have ty := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) y _ hyM
  have tz := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) z _ hzM
  unfold GPsi
  rw [if_neg hψ, if_neg hψ, ty, tz]
  have e : (∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 : ℝ) : ℂ) + (y : ℂ) * ell ψ)
      - (∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (z / n - 1) 0 : ℝ) : ℂ) + (z : ℂ) * ell ψ)
      = ∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        + ((y - z : ℝ) : ℂ) * ell ψ := by
    have : ∀ n : ℕ, (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)
        = (Λ n : ℂ) * primVal D ψ n * ((max (y / n - 1) 0 : ℝ) : ℂ)
          - (Λ n : ℂ) * primVal D ψ n * ((max (z / n - 1) 0 : ℝ) : ℂ) := by
      intro n; push_cast; ring
    simp only [this, Finset.sum_sub_distrib]
    push_cast; ring
  rw [e]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖∑ n ∈ Icc 1 ⌊max y z⌋₊, (Λ n : ℂ) * primVal D ψ n
      * ((max (y / n - 1) 0 - max (z / n - 1) 0 : ℝ) : ℂ)‖ ≤ |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ := by
    refine le_trans (norm_sum_le _ _) ?_
    unfold Formalism.LogFactorialMertensBounds.A
    rw [← Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (y / n - 1) 0 - max (z / n - 1) 0| ≤ |y - z| / n := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : y / n - 1 - (z / n - 1) = (y - z) / n := by ring
      rw [this, abs_div, abs_of_pos hn0]
    calc ‖(Λ n : ℂ) * primVal D ψ n‖ * |max (y / n - 1) 0 - max (z / n - 1) 0|
        ≤ Λ n * (|y - z| / n) := mul_le_mul (norm_coef_le D ψ n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      _ = |y - z| * (Λ n / n) := by ring
  have h2 : ‖((y - z : ℝ) : ℂ) * ell ψ‖ = |y - z| * ‖ell ψ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 := Formalism.LogFactorialMertensBounds.mertens_upper _ hM1
  have h4 : Real.log (⌊max y z⌋₊ : ℝ) ≤ Real.log (max y z) :=
    Real.log_le_log (by exact_mod_cast hM1) (Nat.floor_le (by linarith))
  rw [h2]
  have h5 : |y - z| * Formalism.LogFactorialMertensBounds.A ⌊max y z⌋₊ ≤ |y - z| * (Real.log (max y z) + (Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith

lemma wG_char (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    (w : ℂ) * GPsi D ell ψ (A / w)
      = ∑ n ∈ Icc 1 M, (Λ n : ℂ) * primVal D ψ n * ((max (A / n - w) 0 : ℝ) : ℂ) + (A : ℂ) * ell ψ := by
  have t := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) (A / w) M hM
  unfold GPsi
  rw [if_neg hψ, t, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact this.ne'
    have : max (A / n - w) 0 = w * max (A / w / n - 1) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [this]; push_cast; ring
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hw.ne']

lemma floor_div_le {A w μ : ℝ} (hA : 0 ≤ A) (hμ : 0 < μ) (h : μ ≤ w) : ⌊A / w⌋₊ ≤ ⌊A / μ⌋₊ :=
  Nat.floor_le_floor (div_le_div_of_nonneg_left hA hμ h)

lemma lip_char (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'| := by
  have hμ : 0 < min w w' := lt_min hw hw'
  rw [wG_char D ell ψ hψ A w hw _ (floor_div_le hA.le hμ (min_le_left _ _)),
    wG_char D ell ψ hψ A w' hw' _ (floor_div_le hA.le hμ (min_le_right _ _)), add_sub_add_right_eq_sub,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Icc 1 ⌊A / min w w'⌋₊,
      ‖(Λ n : ℂ) * primVal D ψ n * ((max (A / n - w) 0 : ℝ) : ℂ)
        - (Λ n : ℂ) * primVal D ψ n * ((max (A / n - w') 0 : ℝ) : ℂ)‖ ≤ Λ n * |w - w'| := by
    intro n _
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (A / n - w) 0 - max (A / n - w') 0| ≤ |w - w'| := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : A / n - w - (A / n - w') = -(w - w') := by ring
      rw [this, abs_neg]
    exact mul_le_mul (norm_coef_le D ψ n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have := sum_vM_le (Y := A / min w w') (by positivity)
  calc (∑ n ∈ Icc 1 ⌊A / min w w'⌋₊, Λ n) * |w - w'| ≤ (3 * (A / min w w')) * |w - w'| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = 3 * A / min w w' * |w - w'| := by ring

end

lemma wGz (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    w * Gz (A / w) = ∑ n ∈ Icc 1 M, Λ n * max (A / n - w) 0 - A * Real.log (A / w)
      + (1 + Real.eulerMascheroniConstant) * A := by
  have t := truncR (fun n => Λ n) (A / w) M hM
  unfold Gz Sz
  rw [t]
  have hs : w * ∑ n ∈ Icc 1 M, Λ n * max (A / w / n - 1) 0 = ∑ n ∈ Icc 1 M, Λ n * max (A / n - w) 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact this.ne'
    have : max (A / n - w) 0 = w * max (A / w / n - 1) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [this]; ring
  rw [← hs]
  field_simp

lemma lip_triv_le (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hww : w ≤ w') :
    |w * Gz (A / w) - w' * Gz (A / w')| ≤ 3 * A / w * (w' - w) := by
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  rw [wGz A w hw ⌊A / w⌋₊ le_rfl, wGz A w' hw' ⌊A / w⌋₊ (floor_div_le hA.le hw hww)]
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w') 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro n _
    rw [← mul_sub]
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    have : max (A / n - w') 0 ≤ max (A / n - w) 0 := max_le_max (by linarith) le_rfl
    linarith
  have hS1 : ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w') 0
      ≤ 3 * A / w * (w' - w) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - Λ n * max (A / n - w') 0 ≤ Λ n * (w' - w) := by
      intro n _
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      have h := abs_max_sub_max_le_abs (A / n - w) (A / n - w') 0
      have e : A / n - w - (A / n - w') = w' - w := by ring
      rw [e, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w' - w)] at h
      exact le_trans (le_abs_self _) h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have := sum_vM_le (Y := A / w) (by positivity)
    calc (∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n) * (w' - w) ≤ (3 * (A / w)) * (w' - w) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = 3 * A / w * (w' - w) := by ring
  have hL : A * Real.log (A / w) - A * Real.log (A / w') = A * Real.log (w' / w) := by
    rw [Real.log_div hA.ne' hw.ne', Real.log_div hA.ne' hw'.ne', Real.log_div hw'.ne' hw.ne']; ring
  have hL0 : 0 ≤ A * Real.log (w' / w) :=
    mul_nonneg hA.le (Real.log_nonneg ((one_le_div hw).2 hww))
  have hL1 : A * Real.log (w' / w) ≤ 3 * A / w * (w' - w) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw' hw)
    have h2 : A * Real.log (w' / w) ≤ A * (w' / w - 1) := mul_le_mul_of_nonneg_left h1 hA.le
    have h3 : A * (w' / w - 1) = A / w * (w' - w) := by field_simp
    have h4 : A / w * (w' - w) ≤ 3 * A / w * (w' - w) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      rw [mul_div_assoc]
      have : 0 ≤ A / w := by positivity
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

lemma lip_triv (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    |w * Gz (A / w) - w' * Gz (A / w')| ≤ 3 * A / min w w' * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm w w', abs_of_nonneg (by linarith : (0 : ℝ) ≤ w' - w)]
    exact lip_triv_le A w w' hA hw h
  · rw [min_eq_right h, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - w'), abs_sub_comm]
    exact lip_triv_le A w' w hA hw' h

end AN

theorem lipschitz_weight_all : LipWAll := by
  intro H _ _ _ D ell ψ A w w' hA hw hw'
  by_cases hψ : ψ = 0
  · subst hψ
    have e : ∀ y : ℝ, GPsi D ell 0 y = ((Gz y : ℝ) : ℂ) := fun y => by simp [GPsi]
    rw [e, e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact AN.lip_triv A w w' hA hw hw'
  · exact AN.lip_char D ell ψ hψ A w w' hA hw hw'

theorem derivative_integral_all : DerivIntAll := by
  obtain ⟨K, hK⟩ := Formalism.zetaPrimeSumErrorLipschitz
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨|K| + (Real.log 4 + 4), by positivity, ?_⟩
  intro H _ _ _ D ell
  constructor
  · intro ψ hψ y z hy hz
    refine le_trans (AN.deriv_char D ell ψ hψ y z hy hz) ?_
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_nonneg K
    linarith
  · intro y z hy hz
    refine le_trans (hK y z (by linarith) (by linarith)).2 ?_
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have := le_abs_self K
    linarith

theorem proposition_final_minimum : RiemannHypothesisOfReducedGrowthData := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  refine ⟨Cd, hCd, fun C ε₁ hε₁ hIn => proposition_final C ε₁ hε₁ fun ε hε hεl => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hIn ε hε hεl
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩ := hx₀ x hx
  exact ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩

end Formalism.LFunctionChainParameters.ThickSetMeanBounds
