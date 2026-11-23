import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ScalAtZeroOfLiftMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarOff

section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le' {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem jV_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (t : T0) :
    ∀ z ∈ (R.toCx3 F).Zl j t, R.jV j t z ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) := by
  intro z hz
  have hx1 := range_adjoint_smul_le' (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hz
  exact (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t z)).1 hx1

end SlopeTestRemainingChoices

theorem galD_base : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  intro hHowe hCRL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hC hEx hCS hψ fw hBar hIo hPins hRow0 hPT hU hfacts
  obtain ⟨h5, hrat, h3w, hprov⟩ := hfacts
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  intro j v hv p
  obtain ⟨a, ha⟩ := GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField R F s hOk hC h3w j p
  have hOne := hPT j hU (hRow0 j)
  have hHerm : Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A3.A.fam.L j A3.A.μ0).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0))
      ((A3.A.fam.L j A3.A.μ0).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0)) := hprov j
  have hBH : BlockHyp (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.lifts j A3.A.μ0⟩
  have hfE := GlobalTheory.QuotRational.fE_mem_cmMax _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) A3.A.v0 s hBH hHerm
  obtain ⟨l, hl⟩ := GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces hHowe hCRL T R.toRealDat κ v₀ O F.lv2 _ hcore.1 hψ hCS fw hBar hIo hU hPins j hOne
    (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE (jV_mem_range R F j A3.A.μ0) v.embedding a
  have hmaj := (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE).1 v
  have hco := GlobalTheory.ConjScalarCoord.liftMat_isRatLift_inner R F h5 hrat j
  have hS : ∀ x, (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p → ∀ y,
      ⟪(R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)),
        (R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec y))⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x y := by
    intro x hx y
    have e1 := hco.2 v hv x y
    have e2 := hl x (F.cr.toL (R.toCx3 F).zs false j A3.A.μ0 y) _ _ (ha x hx) (hco.1 x) (hco.1 y)
    have e3 := hmaj x y
    rw [e1, e2]
    erw [e3]
    exact mul_left_comm _ _ _
  intro x hx y
  by_cases hP : R.PartAt F j p v
  · have e : R.lam3 j A3.A.μ0 p v = l := hC.scal.off j p v l hv hP hS
    exact (hS x hx y).trans (congrArg (fun t : ℝ => (t : ℂ) * _) e.symm)
  · have h0 := GlobalTheory.ScalarConjugation.maj_eq_zero _ v x y (by by_contra hn; exact hP ⟨x, hx, hn⟩)
    exact (hS x hx y).trans ((mul_eq_zero_of_right _ h0).trans (mul_eq_zero_of_right _ h0).symm)

end GlobalTheory.ConjScalarOff
