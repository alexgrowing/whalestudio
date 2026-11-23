import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf

noncomputable section

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.BRoad
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.kunf.SecA

attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem isCompact_stdK' (B : Base F E) (Y : Spc F E n) (hB : B.IsGood σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ K, ∀ i j, inFrame b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame b k).map (piInf (B.emb w)) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) => incM F b.1 * M * incM F (b⁻¹).1) '' Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ K, mat2 k ∈ S := fun k hk => ⟨inFrame b k, fun i _ j _ => hentry k hk i j, by
    show incM F b.1 * (incM F (b⁻¹).1 * mat2 k * incM F b.1) * incM F (b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := Y) b
  have hKset : (K : Set (G2 σ Y)) =
      (⋂ w, {k | (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (K : Set (G2 σ Y)) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ Y) K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (K.inv_mem hk)⟩

variable {Y : Spc F E n}

def tBlk (p : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 p * dC n (AE F E)).toRows₁

theorem tBlk_eq_tF_mul_prod_tV {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (hp : IsPar p t) : tBlk p = t.1 := by
  rw [tBlk, isPar_iff.1 hp]
  simp [dC, diagCols, Matrix.fromRows_mul]

theorem continuous_levi_block : Continuous (tBlk (σ := σ) (Y := Y)) := by
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : G2 σ Y => mat2 g * dC n (AE F E) := hm.matrix_mul continuous_const
  exact continuous_pi fun i => continuous_pi fun j => h1.matrix_elem (Sum.inl i) j

def uDet (p : par2 σ Y) : (AE F E)ˣ where
  val := (tBlk p.1).det
  inv := (tBlk p.1⁻¹).det
  val_inv := by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 p.2
    rw [tBlk_eq_tF_mul_prod_tV ht, tBlk_eq_tF_mul_prod_tV ht.inv, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  inv_val := by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 p.2
    rw [tBlk_eq_tF_mul_prod_tV ht, tBlk_eq_tF_mul_prod_tV ht.inv, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

theorem uDet_eq {p : par2 σ Y} {t : GL (Fin n) (AE F E)} (hp : IsPar p.1 t) : uDet p = Matrix.GeneralLinearGroup.det t :=
  Units.ext (by simp [uDet, tBlk_eq_tF_mul_prod_tV hp])

theorem continuous_uDet : Continuous (uDet (σ := σ) (Y := Y)) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_levi_block.comp continuous_subtype_val).matrix_det, ?_⟩
  exact (continuous_levi_block.comp (continuous_inv.comp continuous_subtype_val)).matrix_det

end PositivityTheory.SiegelWeilFormula.kunf.SecA

end
