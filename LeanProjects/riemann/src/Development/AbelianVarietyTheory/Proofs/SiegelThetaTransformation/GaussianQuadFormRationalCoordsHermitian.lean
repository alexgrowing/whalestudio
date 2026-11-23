import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.GaussDict

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem exists_emb_comb_transpose (w : (E →+* ℂ) → ℂ) :
    ∃ c : Fin (Module.finrank ℚ E) → ℂ, ∀ σ : E →+* ℂ,
      ∑ j, σ (Module.finBasis ℚ E j) * c j = w σ := by
  classical
  let e : (E →+* ℂ) ≃ Fin (Module.finrank ℚ E) :=
    Fintype.equivFinOfCardEq (NumberField.Embeddings.card E ℂ)

  let A : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ :=
    Matrix.of fun i j => e.symm i (Module.finBasis ℚ E j)
  have hT : Function.Surjective Aᵀ.mulVec := by
    intro c
    obtain ⟨w', hw'⟩ := GlobalTheory.SW.Dict.exists_emb_comb (E := E) c
    refine ⟨fun i => w' (e.symm i), funext fun j => ?_⟩
    rw [← hw' j]
    exact e.symm.sum_comp (fun σ => σ (Module.finBasis ℚ E j) * w' σ)
  have hA : IsUnit A := by
    have h := Matrix.mulVec_surjective_iff_isUnit.mp hT
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] at h
    exact (Matrix.isUnit_iff_isUnit_det _).mpr h
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA (fun i => w (e.symm i))
  refine ⟨c, fun σ => ?_⟩
  have h := congrFun hc (e σ)
  simpa [Matrix.mulVec, dotProduct, A] using h

theorem exists_coords {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (v v' : Ψ → Fin N → ℂ) :
    ∃ u : QI E N → ℂ, ∀ (τ : Ψ) (a : Fin N),
      ∑ j, τ.1 (Module.finBasis ℚ E j) * u (a, j) = v τ a ∧
      ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (a, j) = v' τ a := by
  classical
  have hc : ∀ σ : E →+* ℂ, σ ∉ Ψ → ComplexEmbedding.conjugate σ ∈ Ψ := fun σ hσ => by
    rw [hΨ, ComplexEmbedding.involutive_conjugate E σ]
    exact hσ

  let w : Fin N → (E →+* ℂ) → ℂ := fun a σ =>
    if h : σ ∈ Ψ then v ⟨σ, h⟩ a else v' ⟨_, hc σ h⟩ a
  choose c hc' using fun a => exists_emb_comb_transpose (w a)
  refine ⟨fun p => c p.1 p.2, fun τ a => ⟨?_, ?_⟩⟩
  · rw [hc' a τ.1]
    simp [w, τ.2]
  · have hn : ComplexEmbedding.conjugate τ.1 ∉ Ψ := (hΨ τ.1).mp τ.2
    have h := hc' a (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h
    rw [h]
    simp only [w, dif_neg hn]
    exact congrArg (fun t => v' t a) (Subtype.ext (ComplexEmbedding.involutive_conjugate E τ.1))

theorem im_tauOf (Ψ : Finset (E →+* ℂ)) (Z : CM Ψ N N) :
    ((tauOf Ψ Z).map fun t => (t.im : ℂ)) = tauOf Ψ (fun τ => imH (Z τ)) := by
  ext p q
  simp only [Matrix.map_apply, tauOf, Matrix.of_apply]
  rw [Complex.im_eq_sub_conj, map_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    Complex.star_def, smul_eq_mul, map_add, map_mul, Complex.conj_conj]
  ring

theorem tauOf_mulVec (Ψ : Finset (E →+* ℂ)) (Y : CM Ψ N N) (u : QI E N → ℂ) (p : QI E N) :
    (tauOf Ψ Y *ᵥ u) p = ∑ τ : Ψ, (τ.1 (Module.finBasis ℚ E p.2) *
      (Y τ *ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) p.1 +
      conj (τ.1 (Module.finBasis ℚ E p.2)) *
      ((Y τ)ᵀ *ᵥ fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) p.1) := by
  simp only [Matrix.mulVec, dotProduct, tauOf, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem zetaOf_dot (Ψ : Finset (E →+* ℂ)) (z z' : CM Ψ n N) (k : Fin n) (u : QI E N → ℂ) :
    zetaOf Ψ z z' k ⬝ᵥ u = ∑ τ : Ψ,
      (z τ k ⬝ᵥ (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) +
      z' τ k ⬝ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) := by
  simp only [dotProduct, zetaOf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

end GlobalTheory.SW.GaussDict

private theorem exists_tauOf_mulVec_eq_zetaOf {E : Type} [Field E] [NumberField E] {Ψ : Finset (E →+* ℂ)}
    (hΨ : IsType Ψ) {m N : ℕ} (Y : CM Ψ N N) (hY : ∀ τ, IsUnit (Y τ)) (z z' : CM Ψ m N)
    (k : Fin m) :
    ∃ u : QI E N → ℂ, tauOf Ψ Y *ᵥ u = zetaOf Ψ z z' k ∧
      zetaOf Ψ z z' k ⬝ᵥ u = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (Y τ)⁻¹ *ᵥ z τ k := by
  obtain ⟨u, hu⟩ := GlobalTheory.SW.GaussDict.exists_coords hΨ (fun τ => ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k)
    (fun τ => (Y τ)⁻¹ *ᵥ z τ k)
  have h1 : ∀ τ : Ψ, (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) =
      ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k := fun τ => funext fun a => (hu τ a).1
  have h2 : ∀ τ : Ψ, (fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) =
      (Y τ)⁻¹ *ᵥ z τ k := fun τ => funext fun a => (hu τ a).2
  have hY1 : ∀ τ, Y τ * (Y τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  have hY2 : ∀ τ, (Y τ)ᵀ * ((Y τ)ᵀ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  refine ⟨u, funext fun p => ?_, ?_⟩
  · rw [GlobalTheory.SW.GaussDict.tauOf_mulVec]
    simp only [h1, h2, Matrix.mulVec_mulVec, hY1, hY2, Matrix.one_mulVec, zetaOf]
    exact Finset.sum_congr rfl fun τ _ => by ring
  · rw [GlobalTheory.SW.GaussDict.zetaOf_dot]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
    ring

theorem GlobalTheory.SW.gauss_form_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N Z hZ z z' k
  rw [GlobalTheory.SW.GaussDict.im_tauOf]
  have hY : ∀ τ : Ψ, IsUnit (imH (Z τ)) := fun τ =>
    ((show ∀ τ : Ψ, (imH (Z τ)).PosDef from hZ) τ).isUnit
  have hsurj : Function.Surjective (tauOf Ψ fun τ => imH (Z τ)).mulVec := fun ξ => by
    obtain ⟨w, w', hw⟩ := GlobalTheory.SW.Dict.zetaOf_surj (n := 1) hΨ (fun _ => ξ)
    obtain ⟨u, hu, -⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY w w' 0
    exact ⟨u, by rw [hu, hw]⟩
  have hU := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  obtain ⟨u, hu, hdot⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY z z' k
  have hinv : (tauOf Ψ fun τ => imH (Z τ))⁻¹ *ᵥ zetaOf Ψ z z' k = u := by
    rw [← hu, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  rw [hinv, hdot]
