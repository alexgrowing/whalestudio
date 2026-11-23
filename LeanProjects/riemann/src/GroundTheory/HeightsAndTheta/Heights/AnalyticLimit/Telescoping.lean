import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

def Telescoping.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (S : System R), ∃ C' ℓ₁ : ℝ, ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ R.Yo,
      (R.r x ≤ ell t → |S.ph t x - S.ph t' x| ≤ C' * (t ^ (1 / 3 : ℝ) + errE S.C t)) ∧
      (ell t < R.r x → |S.ph t x - S.ph t' x| ≤ C' * Real.log (R.r x))

def TelescopingFamily.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (Λ : ℝ),
    ∃ C' ℓ₁ : ℝ, ∀ c : Fin F.m → ℝ, ∑ i, |c i| ≤ Λ →
      ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ F.Yo,
        (F.r x ≤ ell t →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
            C' * (t ^ (1 / 3 : ℝ) + errE C' t)) ∧
        (ell t < F.r x →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * Real.log (F.r x))

theorem ell_anti {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' :=
  Real.log_le_log (inv_pos.2 (lt_of_lt_of_le ht' htt)) (inv_anti₀ ht' htt)

theorem one_le_of_exp_le {y : ℝ} (h : Real.exp 1 ≤ y) : 1 ≤ y := by
  have := Real.add_one_le_exp 1
  linarith

theorem errE_nonneg {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : 0 ≤ errE C t :=
  div_nonneg (mul_nonneg hC (Real.log_nonneg h)) (by linarith)

theorem errE_le {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : errE C t ≤ C := by
  unfold errE
  rw [div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hC

theorem errE_mono {C C' t : ℝ} (hCC : C ≤ C') (h : 1 ≤ ell t) : errE C t ≤ errE C' t :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.log_nonneg h)) (by linarith)

namespace System

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)

def teleConst : ℝ := 1 + |S.C| + S.C ^ 2 + |R.C|

theorem teleConst_pos : 0 < S.teleConst := by
  unfold teleConst
  have := abs_nonneg S.C
  have := abs_nonneg R.C
  have := sq_nonneg S.C
  linarith

theorem C_nonneg {t : ℝ} (ht : 0 < t) (h0 : S.ell₀ ≤ ell t) (h1 : 1 ≤ ell t) (x : X) : 0 ≤ S.C := by
  have h2 := S.ph_le t ht h0 x
  have h3 := S.le_log t ht h0 x
  nlinarith [Real.log_nonneg h1]

theorem dataC_nonneg {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by
  have h2 := R.φ_le x hx
  have h3 := R.le_φ x hx
  nlinarith [Real.log_nonneg (R.one_le_r x hx)]

theorem tele_near {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : R.r x ≤ ell t) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have he0 := errE_nonneg hC h1
  have up1 := S.near t ht h0 x hx hr
  have up2 := S.le_ph t' ht' h0' x hx
  have lo := S.mono t' t ht' htt h0 x
  have hM : S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) =
      (t ^ (1 / 3 : ℝ) + errE S.C t) + S.C * t ^ (1 / 3 : ℝ) + S.C * errE S.C t +
        S.C ^ 2 * (t ^ (1 / 3 : ℝ) + errE S.C t) + R.C * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have p1 := mul_nonneg hC ha
  have p2 := mul_nonneg (sq_nonneg S.C) (add_nonneg ha he0)
  have p3 := mul_nonneg hK (add_nonneg ha he0)
  have p4 := mul_nonneg hC he0
  rw [hM, abs_le]
  constructor <;> linarith

theorem tele_far {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : ell t < R.r x) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * Real.log (R.r x) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have hL : 1 ≤ Real.log (R.r x) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have up1 := S.ph_le t ht h0 x
  have up2 := S.le_ph t' ht' h0' x hx
  have up3 := R.le_φ x hx
  have lo := S.mono t' t ht' htt h0 x
  have hCe : S.C * errE S.C t ≤ S.C * S.C := mul_le_mul_of_nonneg_left (errE_le hC h1) hC
  have hM : S.teleConst * Real.log (R.r x) = Real.log (R.r x) + S.C * Real.log (R.r x) +
      S.C ^ 2 * Real.log (R.r x) + R.C * Real.log (R.r x) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have q1 : S.C ≤ S.C * Real.log (R.r x) := le_mul_of_one_le_right hC hL
  have q2 : S.C ^ 2 ≤ S.C ^ 2 * Real.log (R.r x) := le_mul_of_one_le_right (sq_nonneg _) hL
  have q3 : S.C * S.C = S.C ^ 2 := (sq S.C).symm
  rw [hM, abs_le]
  constructor <;> nlinarith

end System

theorem Telescoping.proof : Telescoping.Statement := by
  intro X _ D A R S
  refine ⟨S.teleConst, max S.ell₀ (Real.exp 1), fun t t' ht' htt hℓ x hx => ⟨?_, ?_⟩⟩
  · exact S.tele_near ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx
  · exact S.tele_far ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx

theorem TelescopingFamily.proof : TelescopingFamily.Statement := by
  intro X _ D A F Λ
  set B : ℝ := ∑ i, (F.sys i).teleConst with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => ((F.sys i).teleConst_pos).le
  have hMB : ∀ i, (F.sys i).teleConst ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => (F.sys i).teleConst)
      (fun i _ => ((F.sys i).teleConst_pos).le) (Finset.mem_univ i)
  have hCB : ∀ i, (F.sys i).C ≤ B := fun i => by
    refine le_trans ?_ (hMB i)
    unfold System.teleConst
    have := le_abs_self (F.sys i).C
    have := abs_nonneg (F.R i).C
    have := sq_nonneg (F.sys i).C
    linarith
  set C' : ℝ := (|Λ| + 1) * B with hC'
  have hBC' : B ≤ C' := by
    rw [hC']
    nlinarith [abs_nonneg Λ]
  refine ⟨C', ∑ i, |(F.sys i).ell₀| + Real.exp 1, fun c hc t t' ht' htt hℓ x hx => ?_⟩
  have h0 : ∀ i, (F.sys i).ell₀ ≤ ell t := fun i => by
    refine le_trans (le_trans (le_abs_self _) ?_) hℓ
    have := Finset.single_le_sum (f := fun i => |(F.sys i).ell₀|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := Real.exp_pos 1
    linarith
  have he : Real.exp 1 ≤ ell t := by
    refine le_trans ?_ hℓ
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (F.sys i).ell₀)
    linarith
  have h1 := one_le_of_exp_le he
  have hx' : ∀ i, x ∈ (F.R i).Yo := fun i => (F.Yo_eq i).symm ▸ hx
  have hr' : ∀ i, (F.R i).r x = F.r x := fun i => F.r_eq i x hx
  have hsum : |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
      ∑ i, |c i| * |(F.sys i).ph t x - (F.sys i).ph t' x| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have hc0 : ∑ i, |c i| ≤ |Λ| := le_trans hc (le_abs_self Λ)
  have hfin : ∀ K : ℝ, 0 ≤ K → (∀ i, |(F.sys i).ph t x - (F.sys i).ph t' x| ≤ B * K) →
      |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * K := by
    intro K hK hi
    refine le_trans hsum (le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hi i) (abs_nonneg (c i))) ?_)
    rw [← Finset.sum_mul, hC']
    have hBK := mul_nonneg hB0 hK
    nlinarith [mul_le_mul_of_nonneg_right hc0 hBK]
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  refine ⟨fun hr => hfin _ (add_nonneg ha (errE_nonneg (hB0.trans hBC') h1)) fun i => ?_,
    fun hr => hfin _ (Real.log_nonneg (le_trans h1 (le_of_lt hr))) fun i => ?_⟩
  · have hCi := (F.sys i).C_nonneg ht (h0 i) h1 x
    refine le_trans ((F.sys i).tele_near ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr))
      (mul_le_mul (hMB i) ?_ (add_nonneg ha (errE_nonneg hCi h1)) hB0)
    linarith [errE_mono ((hCB i).trans hBC') h1]
  · have h := (F.sys i).tele_far ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr)
    rw [hr' i] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (hMB i)
      (Real.log_nonneg (le_trans h1 (le_of_lt hr))))

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
