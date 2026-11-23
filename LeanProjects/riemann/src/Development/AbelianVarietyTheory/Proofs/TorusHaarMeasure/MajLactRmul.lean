import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MajInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section copy
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)

omit [NumberField E] [IsCMField E] in
theorem col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = Data.emb τ (P *ᵥ Pi.single k 1) := by
  funext i
  simp [ReciprocityTheory.ChartRestriction.G.FD.col, Data.emb]

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply]
  have hc : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.col (γ.map τ * Y) c = (γ.map τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
    intro c; funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab X hγ]

end copy

theorem exists_colP_rmul_eq_sum {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    ∃ L : Fin X.p0 → ℂ, X.colP (rmul x b) τ a = ∑ c, L c • X.colP x τ c := by
  classical
  refine ⟨fun c => b τ (Fin.castLE X.p0_le c) (Fin.castLE X.p0_le a), ?_⟩
  funext k
  have e1 : X.colP (rmul x b) τ a k = ∑ j, x τ k j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) k (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show b τ _ _ * x τ k _ = _
    rw [mul_comm]

theorem maj_rmul {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul x b) τ v = X.maj x τ v := by
  have h := MajorantConjugateTransfer.maj_transfer X hx (OrthogonalFrameDomain.rmul_mem_dom X hx hb) τ 1 1 (by simp) (by simp)
    (fun c => ?_) (fun a => ?_) v
  · simpa using h
  · have := exists_colP_rmul_eq_sum X (rmul x b) (ExtFPf.invF_mem X hb) τ c
    rw [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF] at this
    simpa using this
  · simpa using exists_colP_rmul_eq_sum X x hb τ a

theorem gram_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_stab X hγ.1 τ.1 (mat x τ)

theorem lact_mem_dom {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul, show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    refine mul_ne_zero ?_ (hx τ).1
    have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).det) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    exact (hu.map τ.1).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact X hγ]

theorem maj_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj (lact γ x) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) =
      X.maj x τ v := by
  have hc : ∀ c, col (mat (lact γ x) τ) c =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ col (mat x τ) c := by
    intro c; funext i
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) i c = _
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold Data.maj Data.posPart Data.gramPos
  simp only [hc, gram_lact X hγ, hermC_stab X hγ.1]

end GlobalTheory.MajInv

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem maj_lact_rmul :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) := by
  intro r X γ hγ x hx b hb
  refine ⟨MajInv.lact_mem_dom X hγ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), fun τ v => ?_⟩
  rw [MajInv.maj_lact X hγ, MajInv.maj_rmul X hx hb]

end GlobalTheory
