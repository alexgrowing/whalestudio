import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd

noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {v : Pl F}

theorem isOpen_int (hL : Y.L.IsLattice E) (v : Pl F) : IsOpen (intGrp σ Y v : Set (UA σ Y.J)) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := lat_gen hL
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ce : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  let U : Set (Fin m → AF F) := {a | ∀ i, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (ce.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact gen_mem (idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j))) (x j).2
  have x1 : ∀ i, incV F (x i).1 ∈ V := fun i => ⟨Pi.single i 1, fun j => by
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _], by rw [Fintype.linearCombination_apply_single, one_smul]⟩
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    exact x1 i
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds
    ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩) fun g hg z hz h => ⟨key _ hg.1 z hz h, key _ hg.2 z hz h⟩)

theorem exists_cpt (hL : Y.L.IsLattice E) (v : Pl F) : ∃ C : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact C ∧
    ∀ g ∈ locGrp σ Y v, IntAt v g → mat g ∈ C := by
  obtain ⟨m, x, hs, -⟩ := lat_gen hL
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  choose c hc using fun j : Fin n => gen_surj hL hs (Pi.single j 1)
  refine ⟨_, (isCompact_univ_pi fun _ : Fin m => isCompact_latHat hL).image
    (f := fun y => (1 - idem v) • 1 + Matrix.of fun r j => ∑ i, c j i • y i r)
    (continuous_matrix fun r j => by simp only [Matrix.of_apply, Matrix.add_apply]; fun_prop), fun g hg h => ?_⟩
  refine ⟨fun i => mat g *ᵥ (idem v • incV F (x i).1), fun i _ => (h _ ?_ (at_iff.2 (by rw [smul_smul, idem_sq]))).1, ?_⟩
  · exact gen_mem (mul_one (idem v) ▸ idem_mem (by rw [map_one]; exact one_mem _)) (x i).2
  · refine Eq.trans ?_ (congrArg mat (mem_loc.1 hg))
    show (1 - idem v) • 1 + _ = (1 - idem v) • 1 + idem v • mat g
    refine (add_right_inj _).2 (Matrix.ext fun r j => ?_)
    have e := congrFun (congrArg (fun w => idem v • mat g *ᵥ w) (hc j)) r
    simp only [Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply] at e
    simp only [Matrix.of_apply, Matrix.mulVec_smul, Pi.smul_apply, Matrix.smul_apply, ← e]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem isCompact_int (hL : Y.L.IsLattice E) (v : Pl F) : IsCompact {g : locGrp σ Y v | IntAt v g.1} := by
  obtain ⟨C, hC, h⟩ := exists_cpt (σ := σ) hL v
  have := t2Space_cm_host_adeles (F := F) (E := E)
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
  have hc : IsClosed (UG (cA σ) (incM F Y.J) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs)) continuous_const
  have e := (Units.isClosedEmbedding_embedProduct.comp hc.isClosedEmbedding_subtypeVal).comp
    (isClosed_loc (σ := σ) (Y := Y) (v := v)).isClosedEmbedding_subtypeVal
  refine (e.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))).of_isClosed_subset
    ((isClosed_int hL v).preimage continuous_subtype_val) fun g hg => ⟨h _ g.2 hg, _, h _ (inv_mem g.2) ?_, rfl⟩
  exact (intGrp σ Y v).inv_mem hg

theorem _root_.GlobalTheory.ThK.Dbl.locMeas : LocMeas := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY v
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  let K : TopologicalSpace.PositiveCompacts (locGrp σ Y v) := ⟨⟨_, isCompact_int hY.lat v⟩, 1, mem_interior_iff_mem_nhds.2
    (((isOpen_int hY.lat v).preimage continuous_subtype_val).mem_nhds (intGrp σ Y v).one_mem)⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

end GlobalTheory.ThK.Dbl.Euler

end
