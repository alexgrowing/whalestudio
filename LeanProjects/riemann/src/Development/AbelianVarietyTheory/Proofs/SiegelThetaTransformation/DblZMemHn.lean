import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem aLin_mulVec_of_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = hermC τ.1 X.Gm w (FD.col (mat x₂ τ) a) := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_pos h, hermC, FD.col, mat, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem aLin_mulVec_of_not_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : ¬ (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = ((mat x₁ τ)⁻¹ *ᵥ w) a := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_neg h]

variable {X}

theorem pos_of_upper {x₁ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (x₂ : Frame X.Ψ r) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    0 < (hermC τ.1 X.Gm w w).re := by
  set c := (mat x₁ τ)⁻¹ *ᵥ w with hc
  have hu : IsUnit (mat x₁ τ).det := isUnit_iff_ne_zero.2 (h₁ τ).1
  have hcw : mat x₁ τ *ᵥ c = w := by rw [hc, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hc0 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    rw [hc, ← aLin_mulVec_of_not_lt X x₁ x₂ τ w ha, h a ha]
  have hsum : w = ∑ a : Fin X.p0, c (Fin.castLE X.p0_le a) • X.colP x₁ τ a := by
    rw [← hcw, Data.mulVec_eq_sum_col]
    symm
    refine Finset.sum_of_injOn (Fin.castLE X.p0_le) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun i _ hi => ?_) (fun _ _ => rfl)
    rw [hc0 i, zero_smul]
    intro hlt
    exact hi ⟨⟨i, hlt⟩, by simp, rfl⟩
  have hne : (fun a : Fin X.p0 => c (Fin.castLE X.p0_le a)) ≠ 0 := by
    intro h0
    apply hw
    rw [hsum]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun h0 a, Pi.zero_apply, zero_smul]
  have := quad_re_pos (X.gramPos_posDef h₁ τ) hne
  rw [hsum, hermC_quad]
  exact this

theorem neg_of_lower (x₁ : Frame X.Ψ r) {x₂ : Frame X.Ψ r} (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    (hermC τ.1 X.Gm w w).re < 0 :=
  X.neg_of_perp h₂ τ hw fun b => by
    have hb : ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 := b.2
    rw [Data.colP, ← aLin_mulVec_of_lt X x₁ x₂ τ w hb, h _ hb]

theorem det_aLin_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aLin X x₁ x₂ τ).det ≠ 0 := by
  intro h
  obtain ⟨w, hw, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have a := pos_of_upper h₁ x₂ τ hw fun a _ => congrFun h0 a
  have b := neg_of_lower x₁ h₂ τ hw fun a _ => congrFun h0 a
  linarith

variable (X) in

theorem aLin_swap (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  ext a c
  simp only [aLin, aAnti, map_apply, of_apply]
  split_ifs
  · simp only [map_sum, map_mul, ← emb_cc, X.Gm_herm]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [Complex.conj_conj]

theorem det_aAnti_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aAnti X x₁ x₂ τ).det ≠ 0 := by
  intro h
  apply det_aLin_ne_zero h₂ h₁ τ
  rw [aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

theorem re_hermC_invol_neg {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {d : Fin r → ℂ} (hd : d ≠ 0) :
    (hermC τ.1 X.Gm (((aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ) *ᵥ d) d).re
      < 0 := by
  set A := aLin X x₁ x₂ τ with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_aLin_ne_zero h₁ h₂ τ)
  set y := A *ᵥ d with hy
  set yp : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then y a else 0 with hyp
  set ym : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then 0 else y a with hym
  set d₁ := A⁻¹ *ᵥ yp with hd₁
  set d₂ := A⁻¹ *ᵥ ym with hd₂
  have e₁ : A *ᵥ d₁ = yp := by rw [hd₁, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e₂ : A *ᵥ d₂ = ym := by rw [hd₂, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hsum : d = d₁ + d₂ := by
    have : yp + ym = y := by
      funext a; simp only [hyp, hym, Pi.add_apply]; split_ifs <;> simp
    rw [hd₁, hd₂, ← mulVec_add, this, hy, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hS : (A⁻¹ * Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * A) *ᵥ d
      = d₂ - d₁ := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hd₁, hd₂, ← mulVec_sub, ← hy]
    congr 1
    funext a
    simp only [mulVec_diagonal, hyp, hym, Pi.sub_apply, sgn]
    split_ifs <;> simp
  have p₁ : d₁ ≠ 0 → 0 < (hermC τ.1 X.Gm d₁ d₁).re := fun h =>
    pos_of_upper h₁ x₂ τ h fun a ha => by rw [← hA, e₁]; simp only [hyp, if_neg ha]
  have p₂ : d₂ ≠ 0 → (hermC τ.1 X.Gm d₂ d₂).re < 0 := fun h =>
    neg_of_lower x₁ h₂ τ h fun a ha => by rw [← hA, e₂]; simp only [hym, if_pos ha]
  have hc : (hermC τ.1 X.Gm d₁ d₂).re = (hermC τ.1 X.Gm d₂ d₁).re := by
    rw [← hermC_conj τ.1 X.Gm_herm d₁ d₂, Complex.conj_re]
  have key : (hermC τ.1 X.Gm (d₂ - d₁) (d₁ + d₂)).re =
      (hermC τ.1 X.Gm d₂ d₂).re - (hermC τ.1 X.Gm d₁ d₁).re := by
    rw [hermC_sub_left, hermC_add_right, hermC_add_right]
    simp only [Complex.sub_re, Complex.add_re, hc]
    ring
  rw [hS]
  rw [← hsum] at key
  rw [key]
  by_cases z₁ : d₁ = 0
  · have z₂ : d₂ ≠ 0 := fun z₂ => hd (by rw [hsum, z₁, z₂, add_zero])
    have := p₂ z₂
    rw [z₁, hermC_zero_left, Complex.zero_re]
    linarith
  · have := p₁ z₁
    by_cases z₂ : d₂ = 0
    · rw [z₂, hermC_zero_left, Complex.zero_re]
      linarith
    · have := p₂ z₂
      linarith

theorem posDef_imH {N : ℕ} {Z : Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ v : Fin N → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ Z *ᵥ v).im) : (imH Z).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · unfold imH
    rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp
  · have e : star v ⬝ᵥ Zᴴ *ᵥ v = conj (star v ⬝ᵥ Z *ᵥ v) := by
      simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Complex.star_def, map_sum,
        map_mul, Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have : star v ⬝ᵥ imH Z *ᵥ v = ((star v ⬝ᵥ Z *ᵥ v).im : ℂ) := by
      unfold imH
      rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, e, Complex.sub_conj,
        smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact_mod_cast h v hv

variable (X) in

theorem re_kappa (τ : E →+* ℂ) : (τ X.κ0).re = 0 := by
  have h : conj (τ X.ξ0) = -τ X.ξ0 := by rw [← emb_cc, X.ξ0_im, map_neg]
  have h' := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h'
  have h0 : (τ X.ξ0).re = 0 := by linarith
  rcases X.κ0_xi with e | e <;> simp [e, h0, map_ofNat]

theorem dblZ_mem {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    dblZ X x₁ x₂ ∈ Hn X.Ψ r := by
  intro τ
  refine posDef_imH fun v hv => ?_
  have hd : star v ≠ 0 := by simpa using hv
  have h := re_hermC_invol_neg h₁ h₂ τ hd
  set S := (aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ with hS
  have e : star v ⬝ᵥ dblZ X x₁ x₂ τ *ᵥ v =
      τ.1 X.κ0 / 4 * hermC τ.1 X.Gm (S *ᵥ star v) (star v) := by
    unfold dblZ
    rw [← hS, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
    congr 1
    simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e, Complex.mul_im]
  have k₁ : (τ.1 X.κ0 / 4).re = 0 := by simp [re_kappa X τ.1]
  have k₂ : (τ.1 X.κ0 / 4).im < 0 := by
    have := X.κ0_sign τ
    simp only [Complex.div_ofNat_im]
    linarith
  rw [k₁, zero_mul, zero_add]
  exact mul_pos_of_neg_of_neg k₂ h

end GlobalTheory.SW.DblPoint

namespace GlobalTheory.SW

theorem dblZ_mem_Hn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj :=
  fun _ _ _ _ _ X x₁ h₁ x₂ h₂ => ⟨X.cmType, DblPoint.dblZ_mem h₁ h₂, fun τ =>
    ⟨DblPoint.det_aLin_ne_zero h₁ h₂ τ, DblPoint.det_aAnti_ne_zero h₁ h₂ τ,
      DblPoint.aLin_swap X x₁ x₂ τ⟩⟩

end GlobalTheory.SW
