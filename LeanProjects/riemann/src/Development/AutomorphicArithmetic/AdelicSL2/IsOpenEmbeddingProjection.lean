import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal
private theorem continuous_gl' : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : (fun g : G1 ℚ => (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun g : G1 ℚ => ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext g
    have : (gl g)⁻¹ = gl g⁻¹ := by
      rw [inv_eq_iff_mul_eq_one]
      exact Units.ext (by
        change (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * ((g⁻¹ : G1 ℚ) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one])
    rw [this]
    rfl
  rw [show (fun x : G1 ℚ => ((((gl x)⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ))) = _ from h]
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun g : G1 ℚ => g⁻¹)

private theorem dM_inv' (t : (A ℚ)ˣ) : (dM t)⁻¹ = dM t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← dM_mul, mul_inv_cancel]
  apply Units.ext
  change !![1, 0; 0, ((1 : (A ℚ)ˣ) : A ℚ)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem continuous_dM_val : Continuous (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) := by
  have h : (fun t : (A ℚ)ˣ => ((dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val

private theorem continuous_dM' : Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) := by
  refine Units.continuous_iff.2 ⟨continuous_dM_val, ?_⟩
  have h : (fun t : (A ℚ)ˣ => (((dM t)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))) =
      fun t : (A ℚ)ˣ => ((dM t⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) := by
    funext t
    rw [dM_inv']
  exact h ▸ (continuous_dM_val.comp continuous_inv)

private theorem det_dM' (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (dM t) = t := by
  have h := det_el 1 t
  simpa using h

private theorem det_rest (x : GL (Fin 2) (A ℚ)) :
    Matrix.det (((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ))) : Matrix (Fin 2) (Fin 2) (A ℚ)) = 1 := by
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹) = 1 := by
    rw [map_mul, map_inv, det_dM', mul_inv_cancel]
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

private noncomputable def rt (x : GL (Fin 2) (A ℚ)) : G1 ℚ × (A ℚ)ˣ :=
  (⟨((x * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)), det_rest x⟩,
    GroundTheory.Automorphic.AdelicGLn.det ℚ 2 x)

private theorem continuous_rt : Continuous rt := by
  have hd := GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hd
  exact Units.continuous_val.comp (continuous_id.mul (continuous_dM'.comp hd).inv)

private theorem rt_pre : Function.LeftInverse rt (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) := by
  rintro ⟨g, t⟩
  refine Prod.ext (Subtype.ext ?_) (det_el g t)
  change (((gl g * dM t) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t)))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (g : Matrix (Fin 2) (Fin 2) (A ℚ))
  rw [det_el, mul_inv_cancel_right]
  rfl

private theorem pos_of_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : t ∈ RationalIdeles.positiveSubgroup := by
  have hi : (t⁻¹ : (A ℚ)ˣ) ∈ UU := US.inv_mem (show t ∈ US from ht)
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ⟨?_, ?_⟩, ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (ht.2 v).le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hi.2 v).le
  · rw [RationalIdeles.coe_realPart, ht.1, map_one]
    exact one_pos

private theorem UU_of_pos {t : (A ℚ)ˣ} (hp : t ∈ RationalIdeles.positiveSubgroup)
    (hm : ((IdeleGroup.ideleModule ℚ t : {r : ℝ // 0 < r}) : ℝ) = 1) : t ∈ UU := by
  have hr : (RationalIdeles.realPart t : ℝ) = 1 := by
    rw [← GroundTheory.Automorphic.GL2Classical.ideleModule_eq_realPart_of_mem hp, hm]
  obtain ⟨hs, -⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  refine ⟨RationalIdeles.realEquiv.injective ?_, fun v => ?_⟩
  · rw [map_one, ← RationalIdeles.coe_realPart, hr]
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 hs v
    have ha' : Valued.v (H.cp v (t : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha
    have hb' : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb
    have hm1 : Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    refine le_antisymm ha' ?_
    calc (1 : _) = Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (t : A ℚ)) := hm1.symm
      _ ≤ Valued.v (H.cp v (t : A ℚ)) := mul_le_of_le_one_left' hb'

theorem UpperTheory.isOpenEmbedding_projection :
    IsOpenEmbedding pm := by
  have hf : Topology.IsEmbedding (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) :=
    Function.LeftInverse.isEmbedding rt_pre continuous_rt
      ((continuous_gl'.comp continuous_fst).mul (continuous_dM'.comp continuous_snd))
  have hu : Topology.IsEmbedding (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have he : (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) =
      (fun p : G1 ℚ × (A ℚ)ˣ => gl p.1 * dM p.2) ∘ (Prod.map id Subtype.val : G1 ℚ × US → G1 ℚ × (A ℚ)ˣ) := by
    funext p
    rfl
  have hc : Topology.IsEmbedding (Subtype.val ∘ pm : G1 ℚ × US → GL (Fin 2) (A ℚ)) := by
    rw [he]
    exact hf.comp hu
  have hp : Continuous pm := Continuous.subtype_mk hc.continuous _
  refine ⟨Topology.IsEmbedding.of_comp hp continuous_subtype_val hc, ?_⟩
  have hs : Set.range pm = (fun x : GG => GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))) ⁻¹'
      (RationalIdeles.positiveSubgroup : Set (IdeleGroup ℚ)) := by
    rw [range_pm]
    ext x
    refine ⟨fun h => pos_of_UU h, fun h => UU_of_pos h ?_⟩
    exact GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [hs]
  exact RationalIdeles.isOpen_positiveSubgroup.preimage
    ((GroundTheory.Automorphic.AdelicGLn.continuous_det ℚ 2).comp continuous_subtype_val)
