import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

open Matrix MeasureTheory Topology

noncomputable section

namespace GlobalTheory.JR.MeasExist

theorem isOpen_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have h : IsOpen (Metric.closedBall (0 : k) 1) := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hc : Continuous fun A : Matrix (Fin r) (Fin r) k => A i j := by fun_prop
  convert h.preimage hc using 1
  ext A; simp

theorem isCompact_intMatrix (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace k := ProperSpace.of_locallyCompactSpace k
  have h : IsCompact (Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r =>
      Metric.closedBall (0 : k) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {A : Matrix (Fin r) (Fin r) k | ∀ i j, ‖A i j‖ ≤ 1} = (Set.pi Set.univ fun _ : Fin r =>
      Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : k) 1) := by
    ext A
    exact ⟨fun H i _ j _ => mem_closedBall_zero_iff.2 (H i j),
      fun H i j => mem_closedBall_zero_iff.1 (H i trivial j trivial)⟩
  rw [e]; exact h

theorem isOpen_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] :
    IsOpen (glO r k) := by
  have h1 := (isOpen_intMatrix r k).preimage (Units.continuous_val (M := Matrix (Fin r) (Fin r) k))
  have h2 := (isOpen_intMatrix r k).preimage (Units.continuous_coe_inv (M := Matrix (Fin r) (Fin r) k))
  convert h1.inter h2 using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, forall_and]

theorem isCompact_glO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] :
    IsCompact (glO r k) := by
  have hK := isCompact_intMatrix r k
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin r) (Fin r) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, forall_and, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]

theorem one_mem_intMatrix (r : ℕ) (k : Type) [NormedField k] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) k) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem isOpen_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [IsUltrametricDist k] [StarRing k] :
    IsOpen (uO r k) :=
  (isOpen_intMatrix r k).preimage continuous_subtype_val

theorem isCompact_uO (r : ℕ) (k : Type) [NontriviallyNormedField k] [LocallyCompactSpace k] [StarRing k]
    [ContinuousStar k] : IsCompact (uO r k) :=
  (isClosed_unitary (R := Matrix (Fin r) (Fin r) k)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_intMatrix r k)

@[to_additive exists_addHaar_eq_one  ]
theorem exists_haar_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (hne : K.Nonempty) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ μ K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by rwa [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

theorem nonempty_meas (r : ℕ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] : Nonempty (Meas r F E) := by
  haveI := h.ultraF
  haveI := h.ultraE
  haveI := h.lcF
  haveI := h.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (h.norm_star y).le⟩
  borelize (GL (Fin r) F) (↥(Matrix.unitaryGroup (Fin r) E)) F E
  obtain ⟨μG, hG, vG⟩ := exists_haar_eq_one (isCompact_glO r F) (isOpen_glO r F)
    ⟨1, fun i j => ⟨one_mem_intMatrix r F i j, by simpa using one_mem_intMatrix r F i j⟩⟩
  obtain ⟨μU, hU, vU⟩ := exists_haar_eq_one (isCompact_uO r E) (isOpen_uO r E)
    ⟨1, fun i j => one_mem_intMatrix r E i j⟩
  obtain ⟨μF, hF, vF⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : F) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  obtain ⟨μE, hE, vE⟩ := exists_addHaar_eq_one (isCompact_closedBall (0 : E) 1)
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) ⟨0, by simp⟩
  exact ⟨Meas.mk μG μU μF μE hG hU hF hE vG vU vF vE⟩

end GlobalTheory.JR.MeasExist
