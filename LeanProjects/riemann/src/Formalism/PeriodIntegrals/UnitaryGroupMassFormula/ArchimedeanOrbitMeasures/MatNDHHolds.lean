import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BetaSym

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem no_kernel {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (χ : W → W → ℂ) (hμ : SelfDual μ χ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hT : ST.TestExP μ χ) (t : W) (ht0 : t ≠ 0)
    (ht : ∀ y, χ t y = 1) : False := by
  haveI := hμ.1
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := hT

  have htr : ∀ y, ∫ x, Φ (x - t) * χ x y ∂μ = ∫ x, Φ x * χ x y ∂μ := by
    intro y
    have := integral_sub_right_eq_self (μ := μ) (fun x => Φ x * χ (x + t) y) t
    simp only [sub_add_cancel] at this
    rw [this]
    congr 1; funext x
    rw [hadd, ht, mul_one]
  have hc' : Continuous fun x => Φ (x - t) := hc.comp (continuous_id.sub continuous_const)
  have hs' : HasCompactSupport fun x => Φ (x - t) := hs.comp_homeomorph (Homeomorph.subRight t)
  have hper : ∀ w, Φ (w - t) = Φ w := by
    intro w
    have h1 := hμ.2 (fun x => Φ (x - t)) hc' hs' (by simp only [htr]; exact hI) (-w)
    have h2 := hμ.2 Φ hc hs hI (-w)
    simp only [htr, neg_neg] at h1 h2
    rw [← h1, h2]
  have hpern : ∀ n : ℕ, ∀ w, Φ (w - n • t) = Φ w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [succ_nsmul, ← sub_sub, hper, ih]
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  apply hz
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖-z‖) / ‖t‖)
  rw [← hpern n (-z)]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have h1 : ‖(n : ℝ) • t‖ ≤ ‖-z - n • t‖ + ‖-z‖ := by
    have := norm_sub_le (-z) (-z - n • t)
    simp only [sub_sub_cancel] at this
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this ⊢
    linarith [norm_sub_rev (-z) (-z - (n : ℝ) • t)]
  rw [norm_smul, Real.norm_natCast] at h1
  have h2 : (R + ‖-z‖) < n * ‖t‖ := by rwa [div_lt_iff₀ htpos] at hn
  linarith

open Classical in

def MatNDH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (matI X).det ≠ 0

theorem matNDH_holds : MatNDH := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP hdet0
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  let t : EuclideanSpace ℝ (KapI X) := (EuclideanSpace.equiv (KapI X) ℝ).symm v
  have ht0 : t ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (EuclideanSpace.equiv (KapI X) ℝ) h
    simpa [t] using this
  have hAt : Alin X t = 0 := by
    simp [Alin, t, Matrix.toLin'_apply]
    exact hv
  have hβ : ∀ y, betaI X t y = 0 := by
    intro y
    rw [betaSym_holds, ← inner_Alin, hAt, inner_zero_right]
  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  haveI := hμ'.1
  have hadd : ∀ x x' y : EuclideanSpace ℝ (KapI X), (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) (x + x') y = (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x y * (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x' y := by
    intro x x' y
    simp only [tupCoord_symm_add, BR_add_leftP, psiInf_addP]
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) :=
    { addL := hadd
      addR := fun x y y' => by simp only [tupCoord_symm_add, BR_add_rightP, psiInf_addP]
      norm1 := fun x y => norm_psiInfP ψ hS _
      contL := fun y => hpc.comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)
      contR := fun x => hpc.comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous) }
  have hTest := ST.testEx_bichar (μinf.map (tupCoord X)) hB
  refine no_kernel (μinf.map (tupCoord X)) _ hμ' hadd hTest t ht0 fun y => ?_
  rw [psiInf_eq ψ hS]
  beta_reduce
  have : (∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
      (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm t) ((tupCoord X).symm y) w)).re) = 0 := hβ y
  simp only [this]
  simp

open Classical in
theorem densMu_holds : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by
    rw [det_Alin]; exact isUnit_iff_ne_zero.2 (matNDH_holds X u' ψ hT μinf νinf fibInf hP)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, betaSym_holds]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
