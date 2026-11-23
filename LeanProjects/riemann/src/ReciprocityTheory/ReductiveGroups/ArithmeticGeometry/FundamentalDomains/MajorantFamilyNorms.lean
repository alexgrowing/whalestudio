import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramFlowTransform

namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem hG_of (τ : X.Ψ) : ∀ a b, τ.1 (X.Gm b a) = conj (τ.1 (X.Gm a b)) := by
  intro a b
  rw [← X.Gm_herm a b]
  first
    | simp [NumberField.IsCMField.complexEmbedding_complexConj]
    | rw [NumberField.IsCMField.complexEmbedding_complexConj]
    | simp [NumberField.IsCMField.complexConj_apply]
    | simp [NumberField.IsCMField.conj_complexEmbedding]
    | (simp only [cc]
       exact NumberField.IsCMField.complexEmbedding_complexConj ..)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : (τ.1 X.ξ0) ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  have := norm_pos_iff.mpr h
  linarith

theorem hsg_of {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∀ i (h : i ≤ r), 0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
  intro i h
  unfold Data.dom GG at hx
  simp only [Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 ⟨i, Nat.lt_succ_of_le h⟩
  first
    | exact h1
    | (unfold dmin lminor gram gramF famN at h1
       exact h1)

theorem dmin_eq (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = (gramF τ.1 X.Gm (famN (mat x τ) i (Nat.le_of_lt_succ i.isLt))).det := rfl

theorem famN_flow (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by
  unfold Data.flowV flw famN mat
  funext a c
  show ∑ b, X.flowMatV (e τ) τ (s τ) c b * x τ b (Fin.castLE h a) =
    x τ c (Fin.castLE h a) + (-I * (X.c τ : ℂ) * s τ *
      hermC τ.1 X.Gm (fun d => x τ d (Fin.castLE h a)) (e τ)) * e τ c
  unfold Data.flowMatV hermC
  simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem alpha_re (c : ℝ) (s : ℂ) : (-I * (c : ℂ) * s) + conj (-I * (c : ℂ) * s) =
    ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem det_flowMat (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (he : hermC τ.1 X.Gm e e = 0) :
    (X.flowMatV e τ s).det = 1 := by
  unfold Data.flowMatV hermC at *
  have key : (of fun a b => (if a = b then (1 : ℂ) else 0) - I * (X.c τ : ℂ) * s * e a *
      ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) =
      1 + replicateCol Unit (fun a => -(I * (X.c τ : ℂ) * s * e a)) *
        replicateRow Unit (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) := by
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  have hd : (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
      (fun a => -(I * (X.c τ : ℂ) * s * e a)) = 0 := by
    calc (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
          (fun a => -(I * (X.c τ : ℂ) * s * e a))
        = -(I * (X.c τ : ℂ) * s) * ∑ a, ∑ b, e a * τ.1 (X.Gm a b) * (starRingEnd ℂ) (e b) := by
          simp only [dotProduct]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by rw [he, mul_zero]
  rw [key, det_one_add_replicateCol_mul_replicateRow, hd, add_zero]

section Prof
variable {x : Frame X.Ψ r} (hx : x ∈ X.dom) (e : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
include hx

theorem mt_famN (i : ℕ) (h : i ≤ r) : GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) i h) (e τ) =
    (mN τ.1 X.Gm (mat x τ) (e τ) i : ℂ) := by
  rw [mt_eq (hG_of X τ) _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h), mN, pN, dif_pos h]
  exact Complex.ext rfl (by simp [hC_self_real (hG_of X τ)])

theorem dmin_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ) (i : ℕ) (h : i ≤ r) :
    (gramF τ.1 X.Gm (famN (mat (X.flowV e s x) τ) i h)).det =
      (gramF τ.1 X.Gm (famN (mat x τ) i h)).det *
        ((1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i : ℝ) : ℂ) := by
  rw [famN_flow, det_flw (hG_of X τ) (e τ) he _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h),
    mt_famN X hx e τ i h, alpha_re]
  push_cast; ring

theorem maj_eq (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) :
    X.maj x τ (e τ) = 2 * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have : X.posPart x τ (e τ) = (GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, this, mt_famN X hx e τ X.p0 X.p0_le, he, Complex.ofReal_re, Complex.zero_re, sub_zero]

theorem maj_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ)
    (h1 : 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 ≠ 0) :
    X.maj (X.flowV e s x) τ (e τ) = 2 * (mN τ.1 X.Gm (mat x τ) (e τ) X.p0 /
      (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0)) := by
  have hα := alpha_re (X.c τ) (s τ)
  have hp : X.posPart (X.flowV e s x) τ (e τ) =
      (GramDeterminantReal.mt τ.1 X.Gm (famN (mat (X.flowV e s x) τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, hp, famN_flow, mt_flw (hG_of X τ) (e τ) he _ _
    (unit_of X.p0 (mat x τ) (hsg_of X hx τ) X.p0 X.p0_le), hα, mt_famN X hx e τ X.p0 X.p0_le, he,
    Complex.zero_re, sub_zero]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div,
      Complex.ofReal_re]
  · rw [hα, mt_famN X hx e τ X.p0 X.p0_le, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact_mod_cast h1

end Prof

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
