import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Published

def UnitaryFiniteCovolume (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
    (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
    ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure],
      ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧
        ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ,
          (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
            (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
              (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)

namespace UnitaryFiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_compact_of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r) (τ : X.Ψ) :
    ∃ K : Set (Matrix (Fin r) (Fin r) ℂ), IsCompact K ∧ ∀ g : Matrix (Fin r) (Fin r) ℂ,
      (∀ u w, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ w) = hermC τ.1 X.Gm u w) → g ∈ K := by
  obtain ⟨P, hP, hg⟩ := X.signature τ
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  obtain ⟨ε, hε, hg'⟩ : ∃ ε : ℂ, ε ≠ 0 ∧ gram τ.1 X.Gm P = ε • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rcases hd with h | h
    · refine ⟨-1, by simp, ?_⟩
      rw [hg, h]
      ext a b
      by_cases hab : a = b <;> simp [sgn, hab]
    · refine ⟨1, by simp, ?_⟩
      rw [hg, h]
      ext a b
      by_cases hab : a = b <;> simp [sgn, hab]
  refine ⟨(fun V : Matrix (Fin r) (Fin r) ℂ => P * V.map (starRingEnd ℂ) * P⁻¹) ''
    (Matrix.unitaryGroup (Fin r) ℂ : Set (Matrix (Fin r) (Fin r) ℂ)), ?_, fun g h => ?_⟩
  · refine (GlobalTheory.isCompact_unitaryGroup (Fin r) ℂ).image ?_
    exact (continuous_const.matrix_mul
      (continuous_id.matrix_map Complex.continuous_conj)).matrix_mul continuous_const
  · set U : Matrix (Fin r) (Fin r) ℂ := P⁻¹ * g * P with hU
    have hPU : P * U = g * P := by
      rw [hU, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    have h1 : gram τ.1 X.Gm (g * P) = gram τ.1 X.Gm P := by
      ext a b
      simp only [gram, Matrix.of_apply, GlobalTheory.UnitaryFrames.col_mul', h]
    have h2 : gram τ.1 X.Gm (P * U) = Uᵀ * (gram τ.1 X.Gm P * U.map (starRingEnd ℂ)) := by
      simp only [GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
        Matrix.mul_assoc]
    rw [hPU, h1, hg', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul] at h2
    have h3 : Uᵀ * U.map (starRingEnd ℂ) = 1 := (smul_right_injective _ hε h2).symm
    have hcc : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by
      ext a b
      simp
    refine ⟨U.map (starRingEnd ℂ), ?_, ?_⟩
    · refine Matrix.mem_unitaryGroup_iff'.2 ?_
      rw [← h3]
      congr 1
      ext a b
      simp [Matrix.star_apply]
    · simp only [hcc]
      rw [hPU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem compactSpace_of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) :
    CompactSpace H := by
  choose K hK hmem using exists_compact_of_definite X hd
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert GlobalTheory.UnitaryFrames.isClosed_unitary X using 1
    ext g
    exact hH g
  have hc : IsCompact (Set.pi Set.univ fun τ : X.Ψ =>
      Units.embedProduct (Matrix (Fin r) (Fin r) ℂ) ⁻¹' (K τ ×ˢ (MulOpposite.op '' K τ))) :=
    isCompact_univ_pi fun τ => Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hK τ).prod ((hK τ).image MulOpposite.continuous_op))
  refine isCompact_iff_compactSpace.mp (hc.of_isClosed_subset hcl fun g hg τ _ => ?_)
  exact ⟨hmem τ _ ((hH g).1 hg τ), _, hmem τ _ ((hH g⁻¹).1 (H.inv_mem hg) τ), rfl⟩

theorem of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧
      ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ,
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
            (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  haveI := compactSpace_of_definite X hd H hH
  refine ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top, fun g =>
    ⟨1, ⟨fun x y => by simp, fun x => by simp⟩, g, Set.mem_univ _, fun τ => ?_⟩⟩
  simp

theorem exists_haar {r : ℕ} (X : Data E r) :
    ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧
      ∃ (_ : MeasurableSpace H) (_ : BorelSpace H) (ν : Measure H), ν.IsHaarMeasure := by
  obtain ⟨H, hH⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.1 r X
  haveI := (GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH).1
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  exact ⟨H, hH, inferInstance, inferInstance, Measure.haar, inferInstance⟩

end UnitaryFiniteCovolume

end GlobalTheory.Published
