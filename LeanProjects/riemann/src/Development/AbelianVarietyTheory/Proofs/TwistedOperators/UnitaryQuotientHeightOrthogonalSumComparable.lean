import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeighStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicVectorSizeSeenOrthogonalSummandLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePowStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtOrth

theorem of_sizes (lemM1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C)
  (lemM2 : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N)
  (lemM3 : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ, ∀ (h : GA D A) (η : Fin A.rank → D.host.E), GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η))
  (lemH : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a) :
    ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  intro D S A B o
  obtain ⟨C1, b, hM1⟩ := lemM1 D A
  obtain ⟨c, N, hc, hM2⟩ := lemM2 D S
  obtain ⟨C3, hM3⟩ := lemM3 D S A B o
  obtain ⟨C2, a2, hH⟩ := lemH D S A B o
  set K : ℝ := max (max C3 c) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hC3K : C3 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hcK : c ≤ K := (le_max_right _ _).trans (le_max_left _ _)

  have first : ∀ h, quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := by
    intro h
    set H := quotHeight S (o.emb (h, 1))
    have hH1 : 1 ≤ H := one_le_quotHeight S _
    have hHN : 1 ≤ H ^ N := one_le_pow₀ hH1
    have hKH : 0 < K * H ^ N := mul_pos hK0 (zero_lt_one.trans_le hHN)
    set t := c / (K * H ^ N)
    have ht0 : 0 < t := div_pos hc hKH
    have ht1 : t ≤ 1 := (div_le_one hKH).2 (hcK.trans (le_mul_of_one_le_right hK0.le hHN))
    have hshort : ∀ η : Fin A.rank → D.host.E, η ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
      intro η hη
      have hne : o.iA *ᵥ η ≠ 0 := by
        intro h0
        apply hη
        have := congrArg (fun x => o.qA *ᵥ x) h0
        simpa [Matrix.mulVec_mulVec, o.qA_iA] using this
      have h2 := hM2 (o.emb (h, 1)) _ hne
      have h3 := hM3 h η
      have hv := GlobalTheory.HtOrth.vsize_nonneg (GlobalTheory.HtOrth.seen A h η)
      rw [div_le_iff₀ hKH]
      calc c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) * H ^ N := h2
        _ ≤ C3 * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right h3 (zero_le_one.trans hHN)
        _ ≤ K * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) * H ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3K hv) (zero_le_one.trans hHN)
        _ = _ := by ring
    have h1 := hM1 h t ht0 ht1 hshort
    have htb : 0 < t ^ b := pow_pos ht0 b
    have e : t ^ b * ((K / c) ^ b * H ^ (N * b)) = 1 := by
      rw [← mul_assoc, ← mul_pow, pow_mul]
      have : t * (K / c) = (H ^ N)⁻¹ := by
        simp only [t]; field_simp
      rw [this, ← mul_pow, inv_mul_cancel₀ (zero_lt_one.trans_le hHN).ne', one_pow]
    calc quotHeight A h = quotHeight A h * t ^ b * ((K / c) ^ b * H ^ (N * b)) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ C1 * ((K / c) ^ b * H ^ (N * b)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring

  have second : ∀ h, quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := by
    intro h
    have hC2 : 0 ≤ C2 := by
      have := hH 1
      rw [show ((1 : GA D A), (1 : GA D B)) = 1 from rfl, map_one, height_one, height_one, one_pow, mul_one] at this
      linarith
    obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight A h
    have hγS : o.emb (γ, 1) ∈ GQ S := by
      rw [mem_GQ_iff] at hγ ⊢
      rw [o.mt_emb, mt_one, Matrix.mul_one]
      exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) hγ) (rat_mem _)) (ratMx_mul (rat_mem _) (rat_mem _))
    have e : o.emb (γ * h, 1) = o.emb (γ, 1) * o.emb (h, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    calc quotHeight S (o.emb (h, 1)) ≤ height S (o.emb (γ, 1) * o.emb (h, 1)) := quotHeight_le S _ hγS
      _ = height S (o.emb (γ * h, 1)) := by rw [e]
      _ ≤ C2 * height A (γ * h) ^ a2 := hH _
      _ ≤ C2 * (2 * quotHeight A h) ^ a2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos A _).le h2 _) hC2
      _ = _ := by ring

  refine ⟨max (C1 * (K / c) ^ b) (C2 * 2 ^ a2), max (N * b) a2, fun h => ⟨?_, ?_⟩⟩
  · have hx : 1 ≤ quotHeight S (o.emb (h, 1)) := one_le_quotHeight S _
    have hq := first h
    have hpos : 0 ≤ C1 * (K / c) ^ b := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) (N * b))
      linarith [quotHeight_pos A h]
    calc quotHeight A h ≤ C1 * (K / c) ^ b * quotHeight S (o.emb (h, 1)) ^ (N * b) := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight S (o.emb (h, 1)) ^ (max (N * b) a2) :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hx (le_max_left _ _)) (by positivity)
            (hpos.trans (le_max_left _ _))
  · have hx : 1 ≤ quotHeight A h := one_le_quotHeight A h
    have hq := second h
    have hpos : 0 ≤ C2 * 2 ^ a2 := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg (pow_pos (zero_lt_one.trans_le hx) a2)
      linarith [quotHeight_pos S (o.emb (h, 1))]
    calc quotHeight S (o.emb (h, 1)) ≤ C2 * 2 ^ a2 * quotHeight A h ^ a2 := hq
      _ ≤ max (C1 * (K / c) ^ b) (C2 * 2 ^ a2) * quotHeight A h ^ (max (N * b) a2) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hx (le_max_right _ _)) (by positivity)
            (hpos.trans (le_max_right _ _))

theorem quotHeight_orthDec_cmp : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h,
    quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a :=
  of_sizes GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow GlobalTheory.T.adelicVectorSize_seen_orthogonalSummand_le GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow

end GlobalTheory.HtOrth

end
