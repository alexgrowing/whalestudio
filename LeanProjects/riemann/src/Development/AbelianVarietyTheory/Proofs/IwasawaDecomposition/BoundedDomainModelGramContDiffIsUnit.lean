import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem mContDiffAt_coordOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (σ : GlobalTheory.AllWt.Psi H) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u => coordOf ix u σ) w := fun a b => by
  have : (fun u : ReciprocityTheory.L2DbarEstimates.V n => coordOf ix u σ a b) =
      ((EuclideanSpace.proj (𝕜 := ℂ) (ix.symm (σ, a, b))).restrictScalars ℝ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem one_sub_map_conj_mul_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - z.map (starRingEnd ℂ) * zᵀ) = (1 - z * zᴴ)ᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]

theorem isUnit_det_one_sub_map_conj {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - z.map (starRingEnd ℂ) * zᵀ).det := by
  rw [one_sub_map_conj_mul_transpose, det_transpose, det_one_sub_mul_comm]
  exact (h.det_pos.ne').isUnit

theorem isUnit_det_one_sub_conjTranspose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - zᴴ * z).det :=
  (h.det_pos.ne').isUnit

theorem MContDiffAt.map_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m n : Type*} {k : WithTop ℕ∞}
    {A : V → Matrix m n ℂ} {z : V} (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => (A x).map (starRingEnd ℂ)) z :=
  fun a b => Complex.conjCLE.contDiff.contDiffAt.comp z (h a b)

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern
open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem modelGram_smooth_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  intro E _ _ _ H Dw n ix w hw τ
  by_cases h : τ (H.rt : E) = H.rt0
  · have hZ := mContDiffAt_coordOf ix ⟨τ, h⟩ w
    have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨τ, h⟩).map (starRingEnd ℂ) * (coordOf ix u ⟨τ, h⟩)ᵀ) w :=
      (mContDiffAt_const 1).sub ((GlobalTheory.PointChern.MContDiffAt.map_conj hZ).mul hZ.transpose)
    have hu := isUnit_det_one_sub_map_conj _ (hw ⟨τ, h⟩)
    simp only [modelGram, dif_pos h]
    refine ⟨?_, ?_⟩
    · simp only [reindex_apply]
      exact (hA.inv hu).submatrix _ _
    · rw [det_reindex_self]
      exact isUnit_nonsing_inv_det_iff.mpr hu
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have hZ := mContDiffAt_coordOf ix ⟨conjEmb τ, h'⟩ w
      have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨conjEmb τ, h'⟩)ᴴ * coordOf ix u ⟨conjEmb τ, h'⟩) w :=
        (mContDiffAt_const 1).sub (hZ.conjTranspose.mul hZ)
      have hu := isUnit_det_one_sub_conjTranspose _ (hw ⟨conjEmb τ, h'⟩)
      simp only [modelGram, dif_neg h, dif_pos h']
      refine ⟨?_, ?_⟩
      · simp only [reindex_apply]
        exact (hA.inv hu).submatrix _ _
      · rw [det_reindex_self]
        exact isUnit_nonsing_inv_det_iff.mpr hu
    · simp only [modelGram, dif_neg h, dif_neg h']
      exact ⟨mContDiffAt_const 1, by simp⟩

end GlobalTheory.PointChern
