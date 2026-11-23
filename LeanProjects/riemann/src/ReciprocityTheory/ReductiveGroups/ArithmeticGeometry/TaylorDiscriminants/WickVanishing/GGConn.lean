import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConnA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma sgn_cast_eq (p0 r : ℕ) : (fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) = sv p0 := by
  funext a
  unfold sgn sv
  split_ifs <;> simp

lemma pos_conj_mul {s : ℝ} {c d : ℂ} (hc : c ≠ 0) (h : 0 < s * d.re) : 0 < s * (c * d * conj c).re := by
  have hn := Complex.normSq_pos.mpr hc
  rw [mul_comm c d, mul_assoc, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h2 : s * (d.re * Complex.normSq c) = (s * d.re) * Complex.normSq c := by ring
  rw [h2]
  exact mul_pos h hn

lemma mem_dom_of_ok {r : ℕ} (X : Data E r) (P : X.Ψ → Matrix (Fin r) (Fin r) ℂ)
    (hP : ∀ τ, (P τ).det ≠ 0 ∧ gram τ.1 X.Gm (P τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, Ok X.p0 (y τ)) :
    (fun τ => (P τ * y τ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ X.dom := by
  intro τ
  have hg : gram τ.1 X.Gm (P τ * y τ) = Gy X.p0 (y τ) := by
    rw [FrameDegreeData.gram_mul, (hP τ).2, sgn_cast_eq]
    rfl
  refine ⟨?_, fun i => ?_⟩
  · show (P τ * y τ).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (hP τ).1 (det_ne_of_ok (hy τ))
  · show 0 < psgn X.p0 i * (lminor (gram τ.1 X.Gm (P τ * y τ)) i).re
    rw [hg]
    unfold psgn sgn lminor
    exact lead_pos (hy τ) i (Nat.le_of_lt_succ i.isLt)

lemma rmul_mem {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [FrameDegreeData.dmin_rmul X x hb τ i]
    exact pos_conj_mul (Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _) ((hx τ).2 i)

theorem flag_domain_frames_connected : GGConnStatement (E := E) := by
  intro r X
  choose P hP using X.signature
  let K : Set (X.Ψ → Matrix (Fin r) (Fin r) ℂ) := {y | ∀ τ, Ok X.p0 (y τ)}
  let φ : (X.Ψ → Matrix (Fin r) (Fin r) ℂ) → Frame X.Ψ r := fun y τ => (P τ * y τ : Matrix (Fin r) (Fin r) ℂ)
  have hφc : Continuous φ := continuous_pi fun τ => continuous_const.matrix_mul (continuous_apply τ)
  have hK : ∀ y ∈ K, φ y ∈ X.dom := fun y hy => mem_dom_of_ok X P hP y hy
  have hKc : IsPreconnected (φ '' K) := isPreconnected_ok.image φ hφc.continuousOn
  have hss : ∀ a : Fin r, sv X.p0 a * sv X.p0 a = 1 := fun a => by
    unfold sv
    split_ifs <;> norm_num
  have h1 : (1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) ∈ K := fun τ =>
    ok_of_blk (fun k a hka => by
      have hne : k ≠ a := by
        rintro rfl
        exact hka Iff.rfl
      simp [Matrix.one_apply_ne hne]) (by simp)
  refine ⟨⟨φ 1, hK 1 h1⟩, isPreconnected_of_forall (φ 1) fun x hx => ?_⟩
  obtain ⟨b, hb, hort⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  let y0 : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (P τ)⁻¹ * mat (rmul x b) τ
  have hy0τ : ∀ τ, P τ * y0 τ = mat (rmul x b) τ := fun τ =>
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hP τ).1)
  have hy0 : φ y0 = rmul x b := funext fun τ => hy0τ τ
  have hy0K : y0 ∈ K := by
    intro τ
    have hg : Gy X.p0 (y0 τ) = diagonal (sv X.p0) := by
      have h2 : gram τ.1 X.Gm (P τ * y0 τ) = Gy X.p0 (y0 τ) := by
        rw [FrameDegreeData.gram_mul, (hP τ).2, sgn_cast_eq]
        rfl
      rw [← h2, hy0τ τ, hort τ, sgn_cast_eq]
    unfold Ok
    rw [hg, diagonal_mul_diagonal]
    simp only [hss]
    rw [diagonal_one]
    exact PosDef.one
  have hB : IsPreconnected (Bor X.Ψ r) := isPreconnected_upper (ι := X.Ψ) (r := r)
  have h1B : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := fun τ =>
    ⟨by
      show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
  have hxB : rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
    funext τ
    exact Matrix.mul_one (mat x τ)
  have hrc : Continuous fun b' : Frame X.Ψ r => rmul x b' :=
    continuous_pi fun τ => continuous_const.matrix_mul (continuous_apply τ)
  refine ⟨(fun b' => rmul x b') '' Bor X.Ψ r ∪ φ '' K, ?_, Or.inr ⟨1, h1, rfl⟩, Or.inl ⟨_, h1B, hxB⟩, ?_⟩
  · rintro z (⟨b', hb', rfl⟩ | ⟨y, hy, rfl⟩)
    · exact rmul_mem X hx hb'
    · exact hK y hy
  · exact IsPreconnected.union (rmul x b) ⟨b, hb, rfl⟩ ⟨y0, hy0K, hy0⟩ (hB.image _ hrc.continuousOn) hKc

end

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
