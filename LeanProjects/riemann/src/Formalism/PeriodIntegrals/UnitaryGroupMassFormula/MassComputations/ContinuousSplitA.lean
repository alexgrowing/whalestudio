import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

noncomputable section

namespace MassDataMassesW

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.BasicNotions

theorem continuous_splitA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (splitA σ J) := by
  unfold splitA
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · have hφ : Continuous (tensMap (E := E) (fstA F)) := by
      have hsm : ∀ (a : AF F) (x : TensorProduct F (AF F) E),
          tensMap (E := E) (fstA F) (a • x) = (fstA F a) • tensMap (E := E) (fstA F) x := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      have hc : Continuous (fstA F : AF F → Ainf F) := continuous_fst
      haveI : IsModuleTopology (AF F) (TensorProduct F (AF F) E) := ⟨rfl⟩
      haveI : IsModuleTopology (Ainf F) (TensorProduct F (Ainf F) E) := ⟨rfl⟩
      have key : Continuous (fun p : AF F × TensorProduct F (Ainf F) E => (fstA F p.1) • p.2) :=
        continuous_smul.comp ((hc.comp continuous_fst).prodMk continuous_snd)
      letI : Module (AF F) (TensorProduct F (Ainf F) E) :=
        Module.compHom _ (fstA F).toRingHom
      haveI : ContinuousSMul (AF F) (TensorProduct F (Ainf F) E) := ⟨key⟩
      let f : TensorProduct F (AF F) E →ₗ[AF F] TensorProduct F (Ainf F) E :=
        { toFun := tensMap (E := E) (fstA F)
          map_add' := map_add _
          map_smul' := hsm }
      exact IsModuleTopology.continuous_of_linearMap f
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map hφ
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hφ
  · have hφ : Continuous (tensMap (E := E) (sndA F)) := by
      have hsm : ∀ (a : AF F) (x : TensorProduct F (AF F) E),
          tensMap (E := E) (sndA F) (a • x) = (sndA F a) • tensMap (E := E) (sndA F) x := by
        intro a x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
      have hc : Continuous (sndA F : AF F → Af F) := continuous_snd
      haveI : IsModuleTopology (AF F) (TensorProduct F (AF F) E) := ⟨rfl⟩
      haveI : IsModuleTopology (Af F) (TensorProduct F (Af F) E) := ⟨rfl⟩
      have key : Continuous (fun p : AF F × TensorProduct F (Af F) E => (sndA F p.1) • p.2) :=
        continuous_smul.comp ((hc.comp continuous_fst).prodMk continuous_snd)
      letI : Module (AF F) (TensorProduct F (Af F) E) :=
        Module.compHom _ (sndA F).toRingHom
      haveI : ContinuousSMul (AF F) (TensorProduct F (Af F) E) := ⟨key⟩
      let f : TensorProduct F (AF F) E →ₗ[AF F] TensorProduct F (Af F) E :=
        { toFun := tensMap (E := E) (sndA F)
          map_add' := map_add _
          map_smul' := hsm }
      exact IsModuleTopology.continuous_of_linearMap f
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map hφ
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hφ

theorem continuous_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Continuous (X.toInf hb) := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
  exact continuous_fst.comp ((continuous_splitA _ _).comp
    ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))

theorem measurable_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf X hb).measurable

theorem volHTie_holds : VolHTie := by
  intro D X hb u hMT
  have h := (hMT.2.2.2 u).2
  have h1 := congrArg (fun m => m Set.univ) h
  rw [Measure.map_apply (measurable_toInf X hb) MeasurableSet.univ, Set.preimage_univ] at h1
  rw [← h1]
  unfold Formalism.L2.SG.Measures.amb
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]

end MassDataMassesW
