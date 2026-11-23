import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem period_eq_triangular_orthonormal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → D.p = Dw.p → D.q = Dw.q → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → (r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0) → ∃ d : Fin g → ℝ, (∀ j, 0 < d j) ∧ ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D (fun j => relab c σ (e j).1) P → ∃ x₀ ∈ X.dom, IsUnitFr X x₀ ∧ ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ (∀ a j, (h₀ *ᵥ P a) j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ ∀ a b, (hermForm (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) (h₀ *ᵥ P a) (h₀ *ᵥ P b)).im = D.EF a b := by
  intro E _ _ _ H Dw l c σ g e D r X φ hσ hp hq hr hp0 hty hef hneg
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    haveI : IsEmpty (Fin g) := idx.isEmpty
    refine ⟨fun _ => 1, fun _ => one_pos, fun P hP => ?_⟩
    obtain ⟨hx, hu⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E 0 X.p0 X.Ψ X.Gm
      X.Gm_herm).2.1 (fun _ a => a.elim0) (fun τ => Subsingleton.elim _ _)
    refine ⟨_, hx, hu, 1, by simp, fun j => isEmptyElim j, fun _ j => isEmptyElim j, fun a b => ?_⟩
    obtain ⟨-, -, -, -, Hm, -, -, hIm⟩ := hP
    rw [← hIm]
    simp [hermForm, dotProduct]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    intro τ hτ
    have := hneg hr0 τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hty' : ∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < D.q then
      ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1 := by
    intro j
    rw [hq]
    rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  have hper : ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
      if ((idx j).2 : ℕ) < D.q then
        hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
    intro x v j
    have h := hi j
    rw [hq]
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl
  let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
  have hφ' : Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧
      (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ' x) (φ' y)) := by
    refine ⟨fun a b hab => φ.injective (Subtype.ext hab), ?_, X.Gm_herm, X.Gm_det, hef⟩
    have hrange : Set.range φ' = X.Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hy
        exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
    rw [hrange]
    exact X.Λ_span
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  refine ⟨fun j => 2 * ‖(idx j).1.1 (-X.ξ0)‖, fun j => ?_, fun P hP => ?_⟩
  · have h1 := hpos _ (idx j).1.2
    have h2 : (idx j).1.1 (-X.ξ0) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have := norm_pos_iff.2 h2
    positivity
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ'
    (by rw [hp, hq, hr]) P hP
  obtain ⟨x₀, b, hb, horth, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r D.q X.Ψ X.Gm X.Gm_herm).1 x hx
  have hs : ∀ j j', PerBor.moveMat D.q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have t1 := hty' j
    have t2 := hty' j'
    have c1 := hi j
    have c2 := hi j'
    by_cases hj : ((idx j).2 : ℕ) < D.q
    · rw [if_pos hj] at h2 t1
      have hj' : ((idx j').2 : ℕ) < D.q := by omega
      rw [if_pos hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
    · rw [if_neg hj] at h2 t1
      have hj' : ¬ ((idx j').2 : ℕ) < D.q := by omega
      rw [if_neg hj'] at t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      rcases c1 with ⟨-, -, c1⟩ | ⟨-, -, c1, d1⟩ <;> rcases c2 with ⟨-, -, c2⟩ | ⟨-, -, c2, d2⟩ <;> omega
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat D.q idx b).det := by
    rw [PerBor.det_of_support _ _ hinj _ hs, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [PerBor.moveMat_diag D.q idx hb]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  have hmove : ∀ a j, (PerBor.moveMat D.q idx b *ᵥ P a) j = if ((idx j).2 : ℕ) < D.q then
      hermC (idx j).1.1 X.Gm (col (mat (rmul x b) (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ' a))
      else ((mat (rmul x b) (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ' a)) (idx j).2 := fun a j =>
    (congrFun (PerBor.moveMat_mulVec D.q idx hb X.Gm x (φ' a) (P a) _ (hPx a) (fun _ => rfl)) j).symm
  have hqq : D.q = X.p0 := hq.trans hp0.symm
  obtain ⟨hx₀, hu₀⟩ := (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (rmul x b) (hqq ▸ horth)
  refine ⟨rmul x b, hx₀, hu₀, PerBor.moveMat D.q idx b, hu, hs, fun a j => ?_, fun a a' => ?_⟩
  · rw [hper, hmove]
    rfl
  · exact GlobalTheory.UnitFrame.im_hermForm_eq E H D r (-X.ξ0) X.Gm φ' X.Ψ hty g idx _ hty' hξ hpos hφ' (rmul x b)
      ((Matrix.mulVecLin (PerBor.moveMat D.q idx b)).toAddMonoidHom.comp P) hmove horth a a'

end GlobalTheory.FrameNorm
