import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.TupStdOfTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem contDiffAt_bilinear_comp_prod {P Q M T : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup T] [NormedSpace ℝ T]
    (B : M →L[ℝ] T →L[ℝ] T) (A : Q → M) (K : P → T) (p0 : P) (q0 : Q)
    (hA : ContDiffAt ℝ 1 A q0) (hK : ContDiffAt ℝ 1 K p0) :
    ContDiffAt ℝ 1 (fun z : P × Q => B (A z.2) (K z.1)) (p0, q0) ∧
    ∀ x t, fderiv ℝ (fun z : P × Q => B (A z.2) (K z.1)) (p0, q0) (x, t) =
      B (fderiv ℝ A q0 t) (K p0) + B (A q0) (fderiv ℝ K p0 x) := by
  have hA' : ContDiffAt ℝ 1 (fun z : P × Q => A z.2) (p0, q0) := hA.comp (p0, q0) contDiffAt_snd
  have hK' : ContDiffAt ℝ 1 (fun z : P × Q => K z.1) (p0, q0) := hK.comp (p0, q0) contDiffAt_fst
  refine ⟨(B.contDiff.contDiffAt.comp (p0, q0) hA').clm_apply hK', fun x t => ?_⟩
  have dA : HasFDerivAt (fun z : P × Q => A z.2) ((fderiv ℝ A q0).comp (ContinuousLinearMap.snd ℝ P Q)) (p0, q0) :=
    (hA.differentiableAt one_ne_zero).hasFDerivAt.comp (p0, q0) (hasFDerivAt_snd)
  have dK : HasFDerivAt (fun z : P × Q => K z.1) ((fderiv ℝ K p0).comp (ContinuousLinearMap.fst ℝ P Q)) (p0, q0) :=
    (hK.differentiableAt one_ne_zero).hasFDerivAt.comp (p0, q0) (hasFDerivAt_fst)
  have dBA := (B.hasFDerivAt.comp (p0, q0) dA)
  have h : HasFDerivAt (fun z : P × Q => B (A z.2) (K z.1)) _ (p0, q0) := dBA.clm_apply dK
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply]
  rw [add_comm]

section Rm

variable {D : D7} (X : HidaSetting D)

theorem rmulT_add_left (a a' : MfI X) (Y : TupI X) : rmulT X (a + a') Y = rmulT X a Y + rmulT X a' Y := by
  funext b i
  simp [rmulT, add_mul, Finset.sum_add_distrib]

theorem rmulT_add_right (a : MfI X) (Y Y' : TupI X) : rmulT X a (Y + Y') = rmulT X a Y + rmulT X a Y' := by
  funext b i
  simp [rmulT, mul_add, Finset.sum_add_distrib]

theorem symm_add_of {A B : Type} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B] [TopologicalSpace B]
    (e : A ≃ₜ B) (he : ∀ x y, e (x + y) = e x + e y) (x y : B) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]

def Rm {μ' : Type} (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') (m : EuclideanSpace ℝ μ')
    (y : EuclideanSpace ℝ (KapI X)) : EuclideanSpace ℝ (KapI X) :=
  tupCoord X (rmulT X (eM.symm m) ((tupCoord X).symm y))

theorem rm_bil {μ' : Type} [Fintype μ'] (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') (heM : ∀ x y, eM (x + y) = eM x + eM y) :
    ∃ B : EuclideanSpace ℝ μ' →L[ℝ] EuclideanSpace ℝ (KapI X) →L[ℝ] EuclideanSpace ℝ (KapI X),
      ∀ m y, B m y = Rm X eM m y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hTs := symm_add_of (tupCoord X) (tupCoord_add X)
  have hMs := symm_add_of eM heM
  have H1 : ∀ m m' y, Rm X eM (m + m') y = Rm X eM m y + Rm X eM m' y := by
    intro m m' y
    simp only [Rm, hMs, rmulT_add_left, tupCoord_add]
  have H3 : ∀ m y y', Rm X eM m (y + y') = Rm X eM m y + Rm X eM m y' := by
    intro m y y'
    simp only [Rm, hTs, rmulT_add_right, tupCoord_add]
  have hc1 : ∀ y, Continuous fun m => Rm X eM m y := fun y =>
    (tupCoord X).continuous.comp ((continuous_right_mul_tuple X).comp
      ((eM.symm.continuous).prodMk continuous_const))
  have hc2 : ∀ m, Continuous fun y => Rm X eM m y := fun m =>
    (tupCoord X).continuous.comp ((continuous_right_mul_tuple X).comp
      (continuous_const.prodMk (tupCoord X).symm.continuous))
  have H2 : ∀ (r : ℝ) m y, Rm X eM (r • m) y = r • Rm X eM m y := fun r m y =>
    map_real_smul (AddMonoidHom.mk' (fun m => Rm X eM m y) fun a b => H1 a b y) (hc1 y) r m
  have H4 : ∀ (r : ℝ) m y, Rm X eM m (r • y) = r • Rm X eM m y := fun r m y =>
    map_real_smul (AddMonoidHom.mk' (fun y => Rm X eM m y) fun a b => H3 m a b) (hc2 m) r y
  let B0 : EuclideanSpace ℝ μ' →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
    LinearMap.mk₂ ℝ (Rm X eM) H1 H2 H3 H4
  refine ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0), fun m y => rfl⟩

end Rm

def KapOrb {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type}
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (KapI X) :=
  tupCoord X (κ x • Y0 X u')

theorem eM_ex {D : D7} (X : HidaSetting D) : ∃ (μ' : Type) (_ : Fintype μ') (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
    ∀ x y, eM (x + y) = eM x + eM y := by
  haveI : NumberField.IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  refine ⟨Fin N, inferInstance, eM.trans (EuclideanSpace.equiv (Fin N) ℝ).symm.toHomeomorph, fun x y => ?_⟩
  show (EuclideanSpace.equiv (Fin N) ℝ).symm (eM (x + y)) =
    (EuclideanSpace.equiv (Fin N) ℝ).symm (eM x) + (EuclideanSpace.equiv (Fin N) ℝ).symm (eM y)
  have h2 : eM ((x + y : MfI X)) = eM x + eM y := hM x y
  rw [h2, map_add]

theorem psiC_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η μ' : Type} [Fintype ι]
    [Fintype η] (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') :
    PsiC X u' a κ eH = fun z => Rm X eM (eM (a (eH.symm z.2))) (KapOrb X u' κ z.1) := by
  funext z
  simp only [PsiC, Rm, KapOrb, Homeomorph.symm_apply_apply, smul_rmulT]

def LieComplementChartContDiffAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ContDiffAt ℝ 1 (KapOrb X u' (kap0 X hb c L)) 0 ∧ kap0 X hb c L 0 • Y0 X u' = Y0 X u'

def LamMap {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι η : Type} [Fintype ι] [Fintype η]
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (dK : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (KapI X))
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ (KapI X) :=
  dK z.1 + (1 / 2 : ℝ) • tupCoord X (rmulT X (TinvI X u' * ((eH.symm z.2 : HmI X) : Matrix _ _ _)) (Y0 X u'))

open Classical in

def LamDet : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), (∀ S T, eH (S + T) = eH S + eH T) →
    νinf.map eH = ENNReal.ofReal cν • volume →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ∃ Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃L[ℝ] EuclideanSpace ℝ (KapI X),
      (∀ z, Φ z = LamMap X u' eH (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0) z) ∧
      ∃ Dv : ℝ, 0 < Dv ∧
        (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ = ENNReal.ofReal Dv • volume ∧
        Real.sqrt |(matI X).det| / (Dv * cν) = tVal X u'

def KapSm : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → ContDiffAt ℝ 1 (KapOrb X u' (kap0 X hb c L)) 0

theorem kappa_c1_of_smooth (h : KapSm) : LieComplementChartContDiffAt := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  exact ⟨h X u' ψ hT μinf νinf fibInf hP hb c S L hc hL, by rw [kap0_zero, one_smul]⟩

theorem tuple_c1_of_kappa (hK : LieComplementChartContDiffAt) : PolarMapContDiffAtBase := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hD η _ eH hadd hb c S ι _ L hc hL
  obtain ⟨μ', _, eM, heM⟩ := eM_ex X
  obtain ⟨B, hB⟩ := rm_bil X eM heM
  obtain ⟨hA, -⟩ := hD eH eM hadd heM
  obtain ⟨hk, -⟩ := hK X u' ψ hT μinf νinf fibInf hP hb c S L hc hL
  have e : PsiC X u' a (kap0 X hb c L) eH =
      fun z => B (eM (a (eH.symm z.2))) (KapOrb X u' (kap0 X hb c L) z.1) := by
    rw [psiC_eq X u' a (kap0 X hb c L) eH eM]
    funext z
    rw [hB]
  unfold PolarChartContDiffAt
  rw [e]
  exact (contDiffAt_bilinear_comp_prod B (fun t => eM (a (eH.symm t))) _ 0 (eH (TI X u' hT)) hA hk).1

theorem tupDet_of (hK : LieComplementChartContDiffAt) (hLam : LamDet) : TupDet := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hD η _ eH cν hadd hν hb c S ι _ L hc hL
  obtain ⟨μ', _, eM, heM⟩ := eM_ex X
  obtain ⟨B, hB⟩ := rm_bil X eM heM
  obtain ⟨hA, hdA⟩ := hD eH eM hadd heM
  obtain ⟨hk, h0⟩ := hK X u' ψ hT μinf νinf fibInf hP hb c S L hc hL
  obtain ⟨Φ, hΦ, Dv, hDv, hvol, har⟩ := hLam X u' ψ hT μinf νinf fibInf hP eH cν hadd hν hb c S L hc hL
  refine ⟨Φ, Dv, ?_, hDv, hvol, har⟩
  have e : PsiC X u' a (kap0 X hb c L) eH =
      fun z => B (eM (a (eH.symm z.2))) (KapOrb X u' (kap0 X hb c L) z.1) := by
    rw [psiC_eq X u' a (kap0 X hb c L) eH eM]
    funext z
    rw [hB]
  rw [e]
  refine ContinuousLinearMap.ext fun z => ?_
  rw [(contDiffAt_bilinear_comp_prod B (fun t => eM (a (eH.symm t))) _ 0 (eH (TI X u' hT)) hA hk).2 z.1 z.2, hdA, map_smul,
    ContinuousLinearMap.smul_apply, hB, hB]
  show _ = Φ (z.1, z.2)
  rw [hΦ, LamMap, add_comm]
  congr 1
  · simp only [Rm, Homeomorph.symm_apply_apply, eH.symm_apply_apply, hC.2.1, rmulT_one, Homeomorph.apply_symm_apply]
  · simp only [Rm, KapOrb, Homeomorph.symm_apply_apply, h0]

theorem tupStd_of_kap (hK : LieComplementChartContDiffAt) (hLam : LamDet) : TupStd :=
  tupStd_of_two (tuple_c1_of_kappa hK) (tupDet_of hK hLam)

theorem tupStd_of_sm (hK : KapSm) (hLam : LamDet) : TupStd := tupStd_of_kap (kappa_c1_of_smooth hK) hLam

end PI.AprimeInfW
