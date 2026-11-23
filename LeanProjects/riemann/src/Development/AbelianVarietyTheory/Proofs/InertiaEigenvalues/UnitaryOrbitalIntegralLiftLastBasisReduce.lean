import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMuStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbeddingStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.OrbULift
theorem actU_uEmb_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis
theorem unitU_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
theorem support_sub : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding
theorem support_bounded : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero
theorem uEmb_isClosedEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding

section Reformulated
variable {E : Type} [NormedField E]

theorem entries_mul_le {n : ℕ} [IsUltrametricDist E] {P Q : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hQ : ∀ i j, ‖Q i j‖ ≤ 1) : ∀ i j, ‖(P * Q) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hQ k j)

theorem entries_mulVec_le {n : ℕ} [IsUltrametricDist E] {P : Matrix (Fin n) (Fin n) E} {v : Fin n → E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) : ∀ i, ‖(P *ᵥ v) i‖ ≤ 1 := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hv k)

variable [StarRing E]

theorem entries_star_le {n : ℕ} [NormedStarGroup E] {P : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) : ∀ i j, ‖(star P) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.star_apply, norm_star]
  exact hP j i

theorem uO_mul {n : ℕ} [IsUltrametricDist E]
    {a b : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) (hb : b ∈ uO n E) : a * b ∈ uO n E :=
  entries_mul_le (P := a.1) (Q := b.1) ha hb

theorem uO_one {n : ℕ} : (1 : Matrix.unitaryGroup (Fin n) E) ∈ uO n E := by
  intro i j
  show ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem uO_inv {n : ℕ} [NormedStarGroup E]
    {a : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) : a⁻¹ ∈ uO n E :=
  entries_star_le (P := a.1) ha

theorem uO_isOpen {n : ℕ} [IsUltrametricDist E] : IsOpen (uO n E) := by
  have e : uO n E = ⋂ i, ⋂ j, (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g; simp [uO]
  rw [e]
  have hc : ∀ i j, Continuous (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) := fun i j =>
    (continuous_subtype_val (p := fun M => M ∈ Matrix.unitaryGroup (Fin n) E)).matrix_elem i j
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall (0 : E) one_ne_zero).preimage (hc i j)

theorem isClosed_unitaryGroup' {n : ℕ} [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) := by
  have e : (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) = {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem uO_isCompact {n : ℕ} [ProperSpace E] [ContinuousStar E] : IsCompact (uO n E) := by
  let B : Set (Matrix (Fin n) (Fin n) E) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : E) 1
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : uO n E = Subtype.val ⁻¹' B := by
    ext g
    show (∀ i j, ‖g.1 i j‖ ≤ 1) ↔
      (∀ i ∈ (Set.univ : Set (Fin n)), ∀ j ∈ (Set.univ : Set (Fin n)), g.1 i j ∈ Metric.closedBall (0 : E) 1)
    simp
  rw [e]
  exact (isClosed_unitaryGroup' (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hB

theorem preimage_uO (r : ℕ) : uEmb r E ⁻¹' uO (r + 1) E = uO r E := by
  ext s
  simp only [Set.mem_preimage, uO, Set.mem_setOf_eq]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    simpa [uEmb, embHom, Matrix.reindex_apply] using this
  · intro h i j
    show ‖(embHom r E s.1) i j‖ ≤ 1
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
    generalize finSumFinEquiv.symm i = a
    generalize finSumFinEquiv.symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simpa using h a b
    · simp
    · simp
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp

theorem actU_mul {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E)
    (Y : Hn n F E) : actU (k * g) Y = actU k (actU g Y) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (k.1 * g.1) * Y.1.1 * star (k.1 * g.1) = k.1 * (g.1 * Y.1.1 * star g.1) * star k.1
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show (k.1 * g.1) *ᵥ Y.2.1 = k.1 *ᵥ (g.1 *ᵥ Y.2.1)
    rw [Matrix.mulVec_mulVec]

theorem actU_one {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (Y : Hn n F E) :
    actU (1 : Matrix.unitaryGroup (Fin n) E) Y = Y := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (1 : Matrix (Fin n) (Fin n) E) * Y.1.1 * star (1 : Matrix (Fin n) (Fin n) E) = Y.1.1
    simp
  · show (1 : Matrix (Fin n) (Fin n) E) *ᵥ Y.2.1 = Y.2.1
    simp

theorem integral_actU {F : Type} [NormedField F] [Algebra F E] [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ}
    (k : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E) (Y : Hn n F E)
    (hY : Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}) :
    actU k Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨?_, ?_, h3⟩
  · exact entries_mul_le (entries_mul_le hk h1) (entries_star_le hk)
  · exact entries_mulVec_le hk h2

end Reformulated

theorem unitU_actU_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E)
    (Y : Hn n F E) : unitU n F E (actU (k * g) Y) = unitU n F E (actU g Y) := by
  rw [actU_mul]
  have hiff : ∀ Z : Hn n F E, actU k Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} ↔
      Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := fun Z =>
    ⟨fun h => by
      have := integral_actU k⁻¹ (uO_inv hk) _ h
      rwa [← actU_mul, inv_mul_cancel, actU_one] at this, fun h => integral_actU k hk Z h⟩
  unfold unitU
  by_cases h : actU g Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _).2 h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hiff _).1 h'))]

theorem compact_support {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F)
    (hΔ : Delta (inv (liftH X ν l).toGl) ≠ 0) :
    HasCompactSupport (fun s => unitU (r + 1) F E (actU (uEmb r E s) (liftH X ν l))) := by
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  obtain ⟨K, hK, hsub⟩ := support_bounded (liftH X ν l) hΔ
  refine HasCompactSupport.intro ((uEmb_isClosedEmbedding r E).isCompact_preimage hK) ?_
  intro s hs
  by_contra h
  exact hs (hsub _ h)

theorem orbU_liftH (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1) (hΔ : Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0) :
  orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology (Matrix (Fin (r+1)) (Fin (r+1)) E) :=
    inferInstanceAs (SecondCountableTopology (Fin (r+1) → Fin (r+1) → E))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin (r+1)) E) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (Matrix.unitaryGroup (Fin (r+1)) E) := by
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group (uO_isCompact (n := r + 1))
      (uO_isOpen.mem_nhds uO_one)
  let R₀ : Subgroup (Matrix.unitaryGroup (Fin (r+1)) E) :=
    { carrier := uO (r+1) E, mul_mem' := uO_mul, one_mem' := uO_one, inv_mem' := uO_inv }
  unfold orbU
  letI := M.mU; haveI := M.bU; letI := M'.mU; haveI := M'.bU
  haveI := M.haarU; haveI := M'.haarU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E (r+1)).2 M
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M'
  rw [GlobalTheory.CosetIntegral.integral_eq_of_coset_support _ _ (uEmb r E) (uEmb_isClosedEmbedding r E) M.μU M'.μU R₀
    uO_isOpen uO_isCompact M.volU (by
      show M'.μU (uEmb r E ⁻¹' uO (r + 1) E) = 1
      rw [preimage_uO]; exact M'.volU)
    _ (fun k hk g => unitU_actU_mul k g hk _) (support_sub X ν l hν) (compact_support X ν l hΔ)]
  simp_rw [actU_uEmb_liftH, unitU_liftH _ ν l hν.le]
  rw [integral_const_mul]
end GlobalTheory.JR.Step.OrbULift
