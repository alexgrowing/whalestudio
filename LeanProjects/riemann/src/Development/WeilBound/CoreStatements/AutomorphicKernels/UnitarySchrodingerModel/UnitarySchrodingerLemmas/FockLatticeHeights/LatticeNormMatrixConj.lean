import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped Matrix ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SwFinM

section Scale

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

def mulVecHomeo (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ (Fin n → R) where
  toFun x := A *ᵥ x
  invFun x := Ai *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, h2]
  right_inv x := by simp [Matrix.mulVec_mulVec, h1]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def mulVecCAE (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ+ (Fin n → R) :=
  { (mulVecHomeo A Ai h1 h2).toEquiv with
    map_add' := fun x y => Matrix.mulVec_add A x y
    continuous_toFun := (mulVecHomeo A Ai h1 h2).continuous
    continuous_invFun := (mulVecHomeo A Ai h1 h2).symm.continuous }

theorem image_eq_preimage (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (S : Set (Fin n → R)) :
    (fun x => A *ᵥ x) '' S = (fun x => Ai *ᵥ x) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show Ai *ᵥ (A *ᵥ y) ∈ S
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · intro hx
    refine ⟨Ai *ᵥ x, hx, ?_⟩
    show A *ᵥ (Ai *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem exists_scale (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (A Ai : Matrix (Fin n) (Fin n) R)
    (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = c * lam S := by
  let e : (Fin n → R) ≃ₜ+ (Fin n → R) := mulVecCAE Ai A h2 h1
  have hcoc : Filter.Tendsto (e : (Fin n → R) → (Fin n → R)) (Filter.cocompact _) (Filter.cocompact _) :=
    (mulVecHomeo Ai A h2 h1).isClosedEmbedding.tendsto_cocompact
  have : (lam.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map lam (e : (Fin n → R) →+ (Fin n → R)) e.continuous e.surjective hcoc
  have hsm := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  set c : ℝ≥0 := (lam.map e).addHaarScalarFactor lam
  have hmap : ∀ S : Set (Fin n → R), (lam.map e) S = lam ((fun x => Ai *ᵥ x) ⁻¹' S) := fun S =>
    MeasurableEquiv.map_apply (mulVecHomeo Ai A h2 h1).toMeasurableEquiv S
  have key : ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = (c : ℝ≥0∞) * lam S := by
    intro S
    rw [image_eq_preimage A Ai h1 h2, ← hmap, hsm]
    rfl
  refine ⟨c, ?_, ENNReal.coe_ne_top, key⟩
  intro h0
  have hu := key Set.univ
  rw [h0, zero_mul, Set.image_univ_of_surjective (f := fun x => A *ᵥ x) (mulVecHomeo A Ai h1 h2).surjective] at hu
  exact isOpen_univ.measure_ne_zero lam Set.univ_nonempty hu

end Scale

section Index

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem lattice_norm_matrix_conj (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (L : AddSubgroup (Fin n → R))
    (A Ai A' C B : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hAC : A' * C = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (L.map (Matrix.mulVecLin A).toAddMonoidHom) (L.map (Matrix.mulVecLin C).toAddMonoidHom)
      (A * B * A') = PositivityTheory.SiegelWeilFormula.Gen.nu2 lam L L B := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_scale lam A Ai h1 h2
  have hS : {x | ∃ y ∈ L.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ L.map (Matrix.mulVecLin C).toAddMonoidHom,
      x = y + (A * B * A').mulVec y'} = (fun x => A *ᵥ x) '' {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + B.mulVec y'} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, AddSubgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, rfl⟩
      refine ⟨u + B *ᵥ u', ⟨u, hu, u', hu', rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨A *ᵥ u, ⟨u, hu, rfl⟩, C *ᵥ u', ⟨u', hu', rfl⟩, ?_⟩
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
  have hL : ((L.map (Matrix.mulVecLin A).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set (Fin n → R)) =
      (fun x => A *ᵥ x) '' (L : Set (Fin n → R)) := by
    rw [AddSubgroup.coe_map]
    rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hS, hL, hc, hc, ENNReal.mul_div_mul_left _ _ hc0 hct]

end Index

end GlobalTheory.CompanionTheory.SwFinM

end
