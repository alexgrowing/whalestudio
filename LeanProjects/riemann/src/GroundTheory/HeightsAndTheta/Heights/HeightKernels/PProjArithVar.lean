import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace ProjectiveArithmeticVariety

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

abbrev xc (j : Fin (n + 1)) : ProjField K (n + 1) :=
  algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j)

def aff (l : Fin n) : ProjField K (n + 1) := xc K n l.succ / xc K n 0

omit [NumberField K] in
theorem xc_ne_zero (j : Fin (n + 1)) : xc K n j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero j)

theorem coord_eq (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin (n + 1)) :
    projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m) * xc K n j := by
  simp only [projSpaceCoord, map_mul, xc]
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

def dehom : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  (aeval (Fin.cases 1 X : Fin (n + 1) → MvPolynomial (Fin n) K)).toRingHom

theorem aff_indep : AlgebraicIndependent ℚ (aff K n) := by
  let L := Localization.Away (X 0 : MvPolynomial (Fin (n + 1)) K)
  have hu : IsUnit (dehom K n (X 0)) := by simp [dehom]
  have hv : IsUnit (xc K n 0) := (xc_ne_zero K n 0).isUnit
  let ψ : L →+* MvPolynomial (Fin n) K := IsLocalization.Away.lift (X 0) hu
  let ι : L →+* ProjField K (n + 1) := IsLocalization.Away.lift (X 0) hv
  let s : Fin n → L := fun l =>
    IsLocalization.mk' L (X l.succ) (⟨X 0, Submonoid.mem_powers _⟩ : Submonoid.powers (X 0 : MvPolynomial (Fin (n + 1)) K))
  have hψ : ψ ∘ s = X := by
    funext l
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (by simp [dehom])
  have hι : ι ∘ s = aff K n := by
    funext l
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    have := xc_ne_zero K n 0
    simp only [aff]
    field_simp
  have hs : AlgebraicIndependent ℚ s := by
    refine AlgebraicIndependent.of_comp ψ.toRatAlgHom ?_
    change AlgebraicIndependent ℚ (ψ ∘ s)
    rw [hψ]
    exact (algebraicIndependent_X (Fin n) K).restrictScalars (algebraMap ℚ K).injective
  have hL : Function.Injective (algebraMap (MvPolynomial (Fin (n + 1)) K) L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have hinj : Function.Injective ι :=
    (IsLocalization.lift_injective_iff _).mpr fun a b =>
      hL.eq_iff.trans (IsFractionRing.injective _ (ProjField K (n + 1))).eq_iff.symm
  rw [← hι]
  exact hs.map' (f := ι.toRatAlgHom) hinj

end ProjectiveArithmeticVariety

open ProjectiveArithmeticVariety in

theorem ProjArithVar.proof (h : CoordConeArithVar.Statement) : ProjArithVar.Statement := by
  intro K _ _ i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m₀⟩ := (integralBasis K).index_nonempty
  have hω : ∀ m, algebraMap K (ProjField K (n + 1)) (integralBasis K m) / algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) := fun m => (map_div₀ _ _ _).symm
  have hω₀ : algebraMap K (ProjField K (n + 1)) (integralBasis K m₀) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (ProjField K (n + 1))).injective).mpr ((integralBasis K).ne_zero m₀)
  have hx₀ := xc_ne_zero K n 0
  have ratio : ∀ m j, projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m / integralBasis K m₀) * (xc K n j / xc K n 0) := by
    intro m j
    rw [coord_eq, coord_eq, ← hω]
    field_simp
  show IsArithVar (mCoordIdeal (projSpaceCoord K (n + 1))) (n + 1)
  refine h Unit (projBlocks K (n + 1)) (ProjField K (n + 1)) (projSpaceCoord K (n + 1)) (fun _ => (m₀, 0)) n
    (aff K n) ⟨()⟩ (fun _ => ?_) (aff_indep K n) (fun l => ?_) ?_
  · rw [coord_eq]; exact mul_ne_zero hω₀ hx₀
  · apply IntermediateField.subset_adjoin
    refine ⟨⟨(), (m₀, l.succ)⟩, ?_⟩
    simp only [ratio, div_self ((integralBasis K).ne_zero m₀), map_one, one_mul, aff]
  · rintro r ⟨⟨u, m, j⟩, rfl⟩
    cases u
    show IsAlgebraic _ (projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ / projSpaceCoord K (n + 1) ⟨(), (m₀, 0)⟩)
    rw [ratio]
    refine IsAlgebraic.mul ?_ ?_
    · exact (IsAlgebraic.algebraMap (A := ProjField K (n + 1))
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (integralBasis K m / integralBasis K m₀))).tower_top
        (L := IntermediateField.adjoin ℚ (Set.range (aff K n)))
    · have hmem : xc K n j / xc K n 0 ∈ IntermediateField.adjoin ℚ (Set.range (aff K n)) := by
        refine Fin.cases ?_ (fun l => ?_) j
        · rw [div_self hx₀]; exact one_mem _
        · exact IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
      exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range (aff K n)))
        (A := ProjField K (n + 1)) ⟨_, hmem⟩

end

end GroundTheory.Heights₂.Heights
