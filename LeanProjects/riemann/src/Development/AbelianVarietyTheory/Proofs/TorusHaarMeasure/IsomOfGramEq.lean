import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MajNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (M *ᵥ a) (M *ᵥ b) = ∑ i, ∑ j, a i * gram τ G M i j * conj (b j) := by
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  have h : ∀ (f : Fin r → Fin r → Fin r → Fin r → ℂ),
      ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ k, ∑ l, ∑ i, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h (fun k l i j => M k i * a i * τ (G k l) * (conj (M l j) * conj (b j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] [IsCMField E] in

theorem isom_of_gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {M N : Matrix (Fin r) (Fin r) ℂ} (hN : N.det ≠ 0) (h : gram τ G M = gram τ G N)
    (u v : Fin r → ℂ) :
    hermC τ G ((M * N⁻¹) *ᵥ u) ((M * N⁻¹) *ᵥ v) = hermC τ G u v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hermC_mulVec, h, ← hermC_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hN),
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

theorem maj_isom {r : ℕ} (X : Data E r) (τ : X.Ψ) {x y : Frame X.Ψ r}
    {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : ∀ u v, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ v) = hermC τ.1 X.Gm u v)
    (hxy : mat y τ = g * mat x τ) (v : Fin r → ℂ) :
    X.maj y τ (g *ᵥ v) = X.maj x τ v := by
  simp only [Data.maj, Data.posPart, Data.gramPos, hxy, gram_isom τ.1 X.Gm hg, col_mul, hg]

theorem mat_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := rfl

theorem continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous

theorem maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by
  intro H r X ε hε
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hd : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  have ht : Filter.Tendsto (cpt X (x0F X)) (𝓝 0) (𝓝 (x0F X)) := by
    have := (continuous_cpt X (x0F X)).tendsto 0
    rwa [IW.cpt_zero] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (H r X _ hd ε hε))
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx z hz => ?_⟩
  obtain ⟨hz0, hm⟩ := hb (y := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hxd : x ∈ X.dom := IW.orth_mem_dom X _ hx
  have hiso : ∀ τ : X.Ψ, ∀ u v, hermC τ.1 X.Gm ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ u)
      ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ v) = hermC τ.1 X.Gm u v := fun τ =>
    isom_of_gram_eq τ.1 X.Gm (hd τ).1 ((hx τ).trans (ho τ).symm)
  have h1 : ∀ τ : X.Ψ, mat x τ = (mat x τ * (mat (x0F X) τ)⁻¹) * mat (x0F X) τ := fun τ => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit (hd τ).1), Matrix.mul_one]
  have h2 : ∀ τ : X.Ψ, mat (cpt X x z) τ =
      (mat x τ * (mat (x0F X) τ)⁻¹) * mat (cpt X (x0F X) z) τ := fun τ => by
    rw [mat_cpt, mat_cpt, ← Matrix.mul_assoc, ← h1]
  have hdet : ∀ τ : X.Ψ, (mat x τ * (mat (x0F X) τ)⁻¹).det ≠ 0 := fun τ h0 => by
    have := (hxd τ).1
    rw [h1, Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ v => ?_⟩
  · rw [h2, Matrix.det_mul]
    exact mul_ne_zero (hdet τ) (hz0 τ).1
  · have := (hz0 τ).2 i
    simp only [dmin] at this ⊢
    rwa [h2, gram_isom τ.1 X.Gm (hiso τ)]
  · obtain ⟨w, rfl⟩ : ∃ w, v = (mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ w :=
      ⟨(mat x τ * (mat (x0F X) τ)⁻¹)⁻¹ *ᵥ v, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mulVec]⟩
    rw [maj_isom X τ (hiso τ) (h1 τ), maj_isom X τ (hiso τ) (h2 τ)]
    exact hm τ w

end GlobalTheory.MajNear
