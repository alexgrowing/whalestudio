import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceCh

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def UstdSub {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | InStd S g}
  one_mem' := by
    intro i _ j
    show (1 : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i hi j
    have e : (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := rfl
    show (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, Matrix.mul_apply]
    simp_rw [hh i hi]
    simp [hg i hi j]
  inv_mem' := by
    intro g hg i hi j
    have e : ((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ := rfl
    have h1 : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul _
    have h2 := congrFun (congrFun h1 j) i
    rw [Matrix.mul_apply] at h2
    simp_rw [hg i hi] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply] at h2
    show ((((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, h2]

def BlockHaarV : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (k : ℕ), S.card = k →
    (∀ i ∈ S, ε i = true) → Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∃ (β : Type) (_ : Fintype β) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
      (P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ β) (ν : Measure (UstdSub ε S)) (r : ℝ)
      (e : EuclideanSpace ℝ β → ℝ) (hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S),
      (∀ z, P₁ (L₁ z) = z) ∧ (∀ M, InBlock ε S M → L₁ (P₁ M) = M) ∧ (∀ z, InBlock ε S (L₁ z)) ∧
      (∀ z, frob (L₁ z) = ‖z‖ ^ 2) ∧
      ν.IsMulLeftInvariant ∧ IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧ 0 < r ∧ Measurable e ∧ (∀ z, 0 ≤ e z) ∧
      ContinuousAt e 0 ∧ 0 < e 0 ∧ (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU k ∧
      Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) ∧
      Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ β) r, MeasurableSet A →
        ν ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) = ∫⁻ y in A, ENNReal.ofReal (e y)

theorem grpHaarH_of (hBH : BlockHaarV) : GrpHaarH := by
  intro D X u' hb c S ι η _ _ L L₁ ctx hS
  obtain ⟨⟨ψ', hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩ := ctx
  have hgd : ∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := hP.2.2.2.1
  choose β hβ L1 P1 ν r e hmem h1 h2 h3 h4 hνL hνF hν0 hr hem hen hec he0 hrat hcont hinj hdens using
    fun v => hBH X.B.I.n (X.B.I.ε v) (S v) D.R.k (hc.1 v).1 (hc.1 v).2 (hgd v)
  letI : ∀ v, Fintype (β v) := hβ
  have hUJ : ∀ v, SecondCountableTopology (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => Formalism.REAL.instSecondCountableUJ _ _
  have : ∀ v, SecondCountableTopology (UstdSub (X.B.I.ε v) (S v)) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((UstdSub (X.B.I.ε v) (S v) : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  have : ∀ v, OpensMeasurableSpace (UstdSub (X.B.I.ε v) (S v)) := fun v => inferInstance
  have : OpensMeasurableSpace (∀ v, UstdSub (X.B.I.ε v) (S v)) := Pi.opensMeasurableSpace
  have : ∀ v, IsFiniteMeasure (ν v) := hνF
  have : ∀ v, (ν v).IsMulLeftInvariant := hνL
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  obtain ⟨hTyb, hTyn⟩ := coord_facts L₁ (fun v M => InBlock (X.B.I.ε v) (S v) M) L1 P1 h1 h2 h3 h4
    (fun y v => hB.1 y v) (fun y => hB.2.1 y) (fun M hM => hB.2.2 M hM)
  set Ty : EuclideanSpace ℝ η →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (β v)) :=
    LinearMap.pi fun v => (P1 v).comp ((LinearMap.proj v).comp L₁) with hTyd
  have hTym := PI.AprimeInfG.measurePreserving_of_normSq Ty hTyb hTyn
  let Tye : EuclideanSpace ℝ η ≃ᵐ (∀ v, EuclideanSpace ℝ (β v)) :=
    (LinearEquiv.ofBijective Ty hTyb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hTye : MeasurePreserving Tye volume (Measure.pi fun _ => volume) := hTym
  have hTyv : ∀ y v, L1 v (Ty y v) = L₁ y v := fun y v => h2 v _ (hB.1 y v)

  let ψf : (∀ v, UstdSub (X.B.I.ε v) (S v)) →
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    fun g => ⟨X.toInf hb (c * (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) * c⁻¹),
      (hc.2 _).2 fun v => (g v).2⟩
  let ψm : (∀ v, UstdSub (X.B.I.ε v) (S v)) →ₙ*
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    { toFun := ψf
      map_mul' := fun g h => by
        apply Subtype.ext
        show toInfHom X hb _ = toInfHom X hb _ * toInfHom X hb _
        rw [← map_mul]
        congr 1
        have : (fun v => (((g * h) v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
            (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) *
              (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := funext fun v => rfl
        rw [this]
        group }
  have hψc : Continuous ψm := by
    apply Continuous.subtype_mk
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v))).mul continuous_const)
  have hψi : Function.Injective ψm := by
    intro g h he
    have e1 := toInf_injective X hb (congrArg Subtype.val he)
    have e2 : (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
        (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := by simpa using e1
    funext v
    exact Subtype.ext (congrFun e2 v)
  have hψs : Function.Surjective ψm := by
    intro hh
    obtain ⟨s, hs⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds
      (hh : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hmemS : X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) ∈
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]
      exact hh.2
    have hstd := (hc.2 _).1 hmemS
    refine ⟨fun v => ⟨(c⁻¹ * s * c) v, hstd v⟩, Subtype.ext ?_⟩
    show X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) = hh
    rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]

  let Φ : ∀ v, EuclideanSpace ℝ (β v) → UstdSub (X.B.I.ε v) (S v) :=
    fun v z => ⟨expU (X.B.I.ε v) (L1 v z), hmem v z⟩
  have hχ : ∀ y, (⟨chiOf X hb c L₁ y, hS y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')) =
      ψm (fun v => Φ v (Ty y v)) := by
    intro y
    apply Subtype.ext
    show chiOf X hb c L₁ y = X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L1 v (Ty y v))) * c⁻¹)
    unfold chiOf
    simp_rw [hTyv]
  set rr := (insert 1 (Finset.univ.image r)).min' ⟨1, Finset.mem_insert_self _ _⟩ with hrr
  have hrr0 : 0 < rr := by
    have hm := Finset.min'_mem (insert 1 (Finset.univ.image r)) ⟨1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hm with e' | e'
    · rw [hrr, e']; norm_num
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 e'
      rw [hrr, ← hv]; exact hr v
  have hrrv : ∀ v, rr ≤ r v := fun v =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ v)))
  have hTyle : ∀ y v, ‖Ty y v‖ ≤ ‖y‖ := by
    intro y v
    have : ‖Ty y v‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← hTyn y]
      exact Finset.single_le_sum (f := fun v => ‖Ty y v‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ v)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hT0 : ∀ v, Ty 0 v = 0 := fun v => by simp
  have hνu : (Measure.pi ν).map ψm Set.univ = ∏ v, ν v Set.univ := by
    rw [Measure.map_apply hψc.measurable MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
  refine ⟨(Measure.pi ν).map ψm, rr, fun y => ∏ v, e v (Ty y v),
    isMulLeftInvariant_map ψm hψc.measurable hψs, inferInstance, ?_, ?_, hrr0, ?_, ?_, ?_, ?_⟩
  · rw [hνu]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hν0 v
  · rw [hνu]
    exact ENNReal.prod_ne_top fun v _ => measure_ne_top _ _
  · refine tendsto_finsetProd _ fun v _ => ?_
    have hv : ContinuousAt (fun y : EuclideanSpace ℝ η => Ty y v) 0 :=
      ((continuous_apply v).comp Ty.continuous_of_finiteDimensional).continuousAt
    have hd : ContinuousAt (e v) (Ty 0 v) := by rw [hT0 v]; exact hec v
    have hdv := ContinuousAt.comp (f := fun y : EuclideanSpace ℝ η => Ty y v) hd hv
    exact hdv
  · simp only [hT0]
    exact Finset.prod_pos fun v _ => he0 v
  · rw [hνu, ENNReal.toReal_prod]
    simp only [hT0]
    rw [← Finset.prod_div_distrib]
    simp only [hrat, Finset.prod_const, Finset.card_univ]
  · intro s hs hsr
    have hB' : Ty '' ball 0 s ⊆ Set.univ.pi fun v => ball 0 (r v) := by
      rintro _ ⟨y, hy, rfl⟩ v -
      exact mem_ball_zero_iff.2 (((hTyle y v).trans_lt (mem_ball_zero_iff.1 hy)).trans_le (hsr.trans (hrrv v)))
    have hΦc : Continuous (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
      continuous_pi fun v => (hcont v).comp (continuous_apply v)
    have hΦi : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v))
        (Set.univ.pi fun v => ball 0 (r v)) := by
      intro z hz z' hz' he'
      funext v
      exact hinj v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he' v)
    have hTA : MeasurableSet (Tye '' ball 0 s) := Tye.measurableSet_image.2 measurableSet_ball
    have hAi : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) :=
      hTA.image_of_continuousOn_injOn hΦc.continuousOn (hΦi.mono hB')
    have himg : (fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s =
        ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => hχ y
    have hmeasH : MeasurableSet (ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) ''
        (Tye '' ball 0 s))) := by
      have e3 : ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) =
          (fun y => ψm (fun v => Φ v (Ty y v))) '' ball 0 s := by
        rw [Set.image_image, Set.image_image]
        rfl
      rw [e3]
      refine measurableSet_ball.image_of_continuousOn_injOn ?_ ?_
      · exact (hψc.comp (hΦc.comp Ty.continuous_of_finiteDimensional)).continuousOn
      · intro y hy y' hy' he'
        have e4 := hψi he'
        have e5 : Ty y = Ty y' := hΦi (hB' ⟨y, hy, rfl⟩) (hB' ⟨y', hy', rfl⟩) e4
        exact hTyb.1 e5
    rw [himg, Measure.map_apply hψc.measurable hmeasH, hψi.preimage_image,
      PI.AprimeInfG.pi_chart_dens ν (fun _ => volume) Φ (fun v => (hcont v).measurable) (fun v => ball 0 (r v))
        (fun v => measurableSet_ball) hinj e hem hdens (Tye '' ball 0 s) hB' hTA hAi,
      ← hTye.setLIntegral_comp_emb Tye.measurableEmbedding]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hen v _]
    rfl

end PI.AprimeInfW
