import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAdaptedBasisUnitarySubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAtOneRealPlaceOverVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsRealPlaceActAsFockPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumeratiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelParamShiftedWeightOfCoverDiscStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelIsometryUnitHighestVectorIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockJointHarmonicVectorsIffPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondencePairingLawOfTensorLawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCoversStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIntegralModelOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatioStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLowerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCoversStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantThetaPairingOfNoTensorIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParametersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParametersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapHarmonicOfDiscreteSeriesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

theorem isGK_fock (p q r s : ℕ) : IsGK (fockAct1 p q r s) ∧ IsGK (fockAct2 p q r s) := by
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  have hw := GlobalTheory.FockPolGK.pol_locFin_weights p q r s
  exact ⟨⟨h1, fun v => (hw.1 v).1, fun v => (hw.1 v).2⟩, ⟨h2, fun v => (hw.2 v).1, fun v => (hw.2 v).2⟩⟩

theorem discreteSeries_harishChandraModule_admissible {X : ProvA} (h5 : admQ5 X) {p q : ℕ} (hn : 1 ≤ p + q) (lam : Ix p q → ℚ) : AdmGK (X.ds p q lam).HK := by
  exact ((h5 p q hn).1 (X.ds p q lam).U ⟨(X.ds p q lam).2, (X.ds p q lam).3⟩).2.2 (X.ds p q lam).HK (X.ds p q lam).ι
    ⟨(X.ds p q lam).9, (X.ds p q lam).10, (X.ds p q lam).11⟩ |>.1

theorem CJoint.symm {p q r s : ℕ} {σ : Type} {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} {Λ₁ Λ₂ Φ} (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, hw1, hw2⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, hw2, hw1⟩

theorem frame_of_adapted {n : ℕ} {G s B : Mn n} (h : IsAdapted G s B) : ∃ ε, IsFrameOf G s ε B⁻¹ := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hBd : IsUnit B.det := by
    have hu : IsUnit (Bᴴ * G * B).det := by
      rw [h1]
      exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hJ, hJ⟩, rfl⟩
    rw [Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hBHd : IsUnit Bᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hBd.star
  refine ⟨ε, Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det B).mpr hBd), ?_, ?_⟩
  · rw [← h1, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBHd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hBd, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one]

section Transport

variable {ι ι' σ σ' Z : Type} {n p q : ℕ} {A : Mn n → (Z → ℂ) → (Z → ℂ)} {φ : Mat p q → Mn n} {c : ℚ}

theorem Side.comp {pt : MvPolynomial ι ℂ → (Z → ℂ)} {pt' : MvPolynomial ι' ℂ → (Z → ℂ)}
    {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ} {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (h : Side A pt κ φ c a) (ς : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial ι ℂ) (hς : ∀ P, pt' P = pt (ς P)) :
    Side A pt' (ς.trans κ) φ c a where
  der Y hY P P' := by
    have e : PolDer A pt' (φ Y) P P' ↔ PolDer A pt (φ Y) (ς P) (ς P') := by simp only [PolDer, hς]
    rw [e]
    exact h.der Y hY (ς P) (ς P')
  wt μ P := by
    simp only [hς]
    exact h.wt μ (ς P)

theorem Side.trans {pt : MvPolynomial ι ℂ → (Z → ℂ)} {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ}
    {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} {a' : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ' ℂ)}
    (h : Side A pt κ φ c a) (w : MvPolynomial σ ℂ ≃ₗ[ℂ] MvPolynomial σ' ℂ) (hw : ∀ Y P, w (a Y P) = a' Y (w P)) :
    Side A pt (κ.trans w) φ c a' where
  der Y hY P P' := by
    rw [h.der Y hY P P']
    simp only [LinearEquiv.trans_apply]
    constructor
    · intro e
      rw [e, map_add, map_smul, hw]
    · intro e
      apply w.injective
      rw [e, map_add, map_smul, hw]
  wt μ P := by
    rw [← h.wt μ P]
    simp only [LinearEquiv.trans_apply, wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    refine forall_congr' fun i => ?_
    rw [← hw, ← LinearEquiv.map_smul, ← map_sub, LinearEquiv.map_eq_zero_iff]

theorem L2UnitaryRepresentationData.comp {G : Mn n} {pt : MvPolynomial ι ℂ → (Z → ℂ)} {pt' : MvPolynomial ι' ℂ → (Z → ℂ)} {ip Θ}
    (h : L2UnitaryRepresentationData G A pt ip Θ) (ς : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial ι ℂ) (hς : ∀ P, pt' P = pt (ς P)) :
    L2UnitaryRepresentationData G A pt' ip Θ := by
  have hd : ∀ X P P', PolDer A pt' X P P' ↔ PolDer A pt X (ς P) (ς P') := fun X P P' => by
    simp only [PolDer, hς]
  exact
  { mem := fun P => by rw [hς]; exact h.mem _
    pt_lin := fun z P Q => by
      simp only [hς, map_add, map_smul]
      exact h.pt_lin z (ς P) (ς Q)
    ip_lin := h.ip_lin
    ip_symm := h.ip_symm
    ip_pos := h.ip_pos
    stable := h.stable
    lin := h.lin
    one := h.one
    mul := h.mul
    unit := h.unit
    cont := h.cont
    der := fun X hX P P' hPP E hE => by
      simp only [hς]
      exact h.der X hX _ _ ((hd X P P').1 hPP) E hE }

theorem Graded.trans {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial ι' ℂ} {w : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ}
    (h : Graded κ) (h' : Graded w) : Graded (κ.trans w) := by
  intro d P
  exact (h' d (κ P)).trans (h d P)

def swp (α β : Type) : MvPolynomial (α × β) ℂ ≃ₗ[ℂ] MvPolynomial (β × α) ℂ :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm α β)).toLinearEquiv

theorem swp_apply {α β : Type} (P : MvPolynomial (α × β) ℂ) : swp α β P = MvPolynomial.rename Prod.swap P := rfl

theorem graded_swp (α β : Type) : Graded (swp α β) := by
  intro d P
  rw [swp_apply]
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Prod.swap_injective

theorem fockIp_swp {α β : Type} (P Q : MvPolynomial (α × β) ℂ) : fockIp (swp α β P) (swp α β Q) = fockIp P Q := by
  classical
  simp only [swp_apply, fockIp]
  rw [MvPolynomial.support_rename_of_injective Prod.swap_injective,
    Finset.sum_image (fun x _ y _ hxy => Finsupp.mapDomain_injective Prod.swap_injective hxy)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ Prod.swap_injective, MvPolynomial.coeff_rename_mapDomain _ Prod.swap_injective,
    Finsupp.prod_mapDomain_index_inj Prod.swap_injective]

end Transport

variable {D : D7}

structure Reads {ι Z : Type} {n n' p q r s : ℕ} (G : Mn n) (G' : Mn n') (A : Mn n → (Z → ℂ) → (Z → ℂ))
    (B : Mn n' → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop)
    (φ : Mat p q → Mn n) (φ' : Mat r s → Mn n') (c c' : ℚ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) : Prop where
  gr : Graded κ
  s₁ : Side A pt κ φ c (fockAct1 p q r s)
  s₂ : Side B pt κ φ' c' (fockAct2 p q r s)
  l2 : ∀ ip, IP ip → ∃ N Θ, Fischer pt ip κ N ∧ L2UnitaryRepresentationData G A pt ip Θ ∧ L2UnitaryRepresentationData G' B pt ip Θ

theorem Reads.swap {ι Z : Type} {n n' p q r s : ℕ} {G : Mn n} {G' : Mn n'} {A : Mn n → (Z → ℂ) → (Z → ℂ)}
    {B : Mn n' → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)} {IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop}
    {φ : Mat p q → Mn n} {φ' : Mat r s → Mn n'} {c c' : ℚ} {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s}
    (h : Reads G G' A B pt IP φ φ' c c' κ) : Reads G' G B A pt IP φ' φ c' c (κ.trans (swp _ _)) where
  gr := h.gr.trans (graded_swp _ _)
  s₁ := h.s₂.trans (swp _ _) fun Y P => by rw [swp_apply, swp_apply, GlobalTheory.FockSwap.rename_fockAct2]
  s₂ := h.s₁.trans (swp _ _) fun Y P => by rw [swp_apply, swp_apply, GlobalTheory.FockSwap.rename_fockAct1]
  l2 ip hip := by
    obtain ⟨N, Θ, hF, h1, h2⟩ := h.l2 ip hip
    refine ⟨N, Θ, ⟨hF.1, fun P Q => ?_⟩, h2, h1⟩
    rw [hF.2 P Q, LinearEquiv.trans_apply, LinearEquiv.trans_apply, fockIp_swp]

def IsIp (S T : HSp D) (ip : (WO S T → ℂ) → (WO S T → ℂ) → ℂ) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕 μ ∧ ip = ipTh μ 𝓕

theorem exists_real {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {τ : D.what₂.Tau} (hω : IsWeilDatumO ψ S T χS χT ω)
    {aS aT : ℚ} (hS : HasInfExp D χS τ aS) (hT : HasInfExp D χT τ aT) {sS frS εS sT frT εT}
    (fS : IsFrameOf (gramAt D S τ) sS εS frS) (fT : IsFrameOf (gramAt D T τ) sT εT frT) {BS BT f}
    (hf : IsFockAt ψ θ S T τ sS sT BS BT f) {p q r s : ℕ} {e : Ix p q ≃ Fin S.rank} {e' : Ix r s ≃ Fin T.rank}
    (he : SignCompat εS e) (he' : SignCompat εT e') :
    ∃ κ, Reads (gramAt D S τ) (gramAt D T τ) (actSrc θ ω τ) (actTgt θ ω τ) (ptAt ψ θ S T τ sS sT BS BT f) (IsIp S T)
      (phiFr frS true e) (phiFr frT false e') aT aS κ := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨ς, hςg, -, hςpt⟩ := GlobalTheory.T.fockVectors_adaptedBasis_unitary_substitution D ψ θ S T τ hψ hf.inf sS frS εS sT frT εT fS fT BS BT hf.onS hf.onT
  obtain ⟨κ₀, hκp, hκg, hκip⟩ := GlobalTheory.T.exists_fockPolynomialIso_graded_isometry p q r s S.rank T.rank εS εT e e' he he'
  have hL := GlobalTheory.T.lieAlgebrasAtPlace_act_fockVectors_by_fockOperators D ψ θ S T χS χT ω τ hf.inf hω aS aT hS hT sS frS εS sT frT εT fS fT f hf.theta hf.vac
  obtain ⟨hth, hrest⟩ := GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum D ψ θ S T τ hψ hf.inf sS frS εS sT frT εT fS fT f hf.theta hf.vac
  obtain ⟨hinj, hfis⟩ := hrest hf.ne
  let L : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ) :=
    pureTensorL (fun k : Fin T.rank × Fin S.rank => aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ k.1 k.2)) f
  have hLpt : ∀ P, L P = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P := fun P => rfl
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.fockVectors_realPlace_act_as_fockPolynomials D ψ θ S T ω τ hf.inf sS frS εS sT frT εT fS fT aS aT L hinj hL p q r s e e' he he' κ₀ hκp
  have hσ := hςpt f hf.theta
  refine ⟨ς.trans κ₀, hςg.trans hκg, hs1.comp ς hσ, hs2.comp ς hσ, ?_⟩
  rintro ip ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  obtain ⟨N, hN⟩ := hfis μ 𝓕 hμ h𝓕
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.realPlaceGroups_act_unitarily_weakly_on_theta D ψ θ S T χS χT ω τ hf.inf hω frS εS frT εT aS aT L hth hL μ 𝓕 hμ h𝓕
  refine ⟨N, Θ, ⟨hN.1, fun P Q => ?_⟩, hΘ1.comp ς hσ, hΘ2.comp ς hσ⟩
  rw [hσ P, hσ Q, hN.2, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hκip]
  rfl

structure Good (D : D7) (X : ProvA) : Prop where
  par : ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam
  ds : DiscreteSeriesBlattner X
  hc : admQ5 X
  br : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D

theorem exists_ktie {X : ProvA} (h : Good D X) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {p q : ℕ} {l₁ l₂ : List ℚ} {c : ℚ} (br cj : Bool) (hn : 1 ≤ p + q) (h₁ : l₁.length = p) (h₂ : l₂.length = q)
    (hp : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ)) (hS : S τ = parOf br cj l₁ l₂ c) :
    (∃ m : ℤ, (m : ℚ) = 2 * c) ∧
      ∃ e u, KTie (X.ds p q (ofBlocks l₁ l₂)) M τ (ofBlocks l₁ l₂) c br cj e u := by
  have hpar := h.par p q _ hp
  have hfin := (h.ds p q _ hp).1
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signCompatible_numbering_decreasing_enumeration V.rank p q l₁ l₂ c br cj (M.ε τ) (M.lam τ) h₁ h₂ hp (by rw [← hS]; exact M.enum τ)
  obtain ⟨m, hm, U, hU⟩ : ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∃ U, Comparison₂ (X.ds p q (ofBlocks l₁ l₂)) M τ br cj e m U := by
    cases br <;> cases cj
    · obtain ⟨m, hm, hU⟩ := GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries D h.br X V S M τ p q l₁ l₂ c hn h₁ h₂ hp hpar (by rw [hS]; rfl)
      exact ⟨m, hm, hU e he.1 false⟩
    · obtain ⟨-, m, hm, hU⟩ := h.br.2 X V S M τ p q l₁ l₂ c ⟨hn, h₁, h₂, hp, hpar, by rw [hS]; rfl⟩
      obtain ⟨U, hU⟩ := hU e he.1
      exact ⟨m, hm, U, fun x y => U.map_add x y, fun z x => U.map_smulₛₗ z x, U.bijective, fun x => U.norm_map x,
        hU.grp, hU.kfin⟩
    · obtain ⟨-, m, hm, hU⟩ := h.br.1 X V S M τ p q l₁ l₂ c ⟨hn, h₁, h₂, hp, hpar, by rw [hS]; rfl⟩
      obtain ⟨U, hU⟩ := hU e he.1
      exact ⟨m, hm, U, fun x y => U.map_add x y, fun z x => U.map_smul z x, U.bijective, fun x => U.norm_map x,
        hU.grp, hU.kfin⟩
    · obtain ⟨m, hm, hU⟩ := GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries D h.br X V S M τ p q l₁ l₂ c hn h₁ h₂ hp hpar (by rw [hS]; rfl)
      exact ⟨m, hm, hU e he.1 true⟩
  have hhi := GlobalTheory.T.discreteSeriesModelIsometry_unit_highestVector_iff D V S M τ p q _ (X.ds p q (ofBlocks l₁ l₂)) _ c br cj e m U hp he hm hU hfin
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_kFiniteIsometry_discreteSeriesModel_detCover D V S M τ p q _ (X.ds p q (ofBlocks l₁ l₂)) _ c br cj e m U hp he hm hU hhi
  exact ⟨⟨m, hm⟩, e, u, hu⟩

section Core

variable {X : ProvA} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {N : DSModel W S'} {τ : D.what₂.Tau}
  {ι Z : Type} {A : Mn V.rank → (Z → ℂ) → (Z → ℂ)} {B : Mn W.rank → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)}
  {IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop} {t : ℕ} {al be ga de : List ℚ} {c c' : ℚ} {b b' : Bool}
  {e : Ix (al.length + be.length) (ga.length + de.length) ≃ Fin V.rank}
  {e' : Ix (al.length + de.length + t) (ga.length + be.length) ≃ Fin W.rank} {κ}

theorem rank_pos (hd : HypA t al be ga de) :
    1 ≤ al.length + be.length + (ga.length + de.length) ∧ 1 ≤ al.length + de.length + t + (ga.length + be.length) := by
  obtain ⟨ht, hl, -⟩ := hd
  constructor <;> omega

theorem lift_up (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de)
    {u u'} (hM : KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b true e u)
    (hN : KTie (X.ds _ _ (lamA' t al be ga de)) N τ (lamA' t al be ga de) c' b' false e' u')
    (hR : Reads (gramAt D V τ) (gramAt D W τ) A B pt IP (phiFr (M.fr τ) b e) (phiFr (N.fr τ) b' e') c c' κ) :
    LiftLaw M τ A pt N B := by
  have hJ := GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM hN hR.s₁ hR.s₂ hR.gr
  obtain ⟨hU, hD, hLn⟩ := h3.1 t al be ga de hd
  have hT := (GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers X _ _ _ _ _ _ (h1.1 t al be ga de hd) hU hD hLn).1
  have hPL := GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw _ _ _ _ _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).1 (isGK_fock _ _ _ _).2 (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd.1).1 _)
    (h.ds _ _ _ hM.par).1 hT
  exact GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM hN hR.s₁ hR.s₂ hJ hPL

theorem lift_down (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {u u'} (hm : ∃ m : ℤ, (m : ℚ) = 2 * c)
    (hM : KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b false e u)
    (hN : KTie (X.ds _ _ (lamA' t al be ga de)) N τ (lamA' t al be ga de) c' b' true e' u')
    (hR : Reads (gramAt D V τ) (gramAt D W τ) A B pt IP (phiFr (M.fr τ) b e) (phiFr (N.fr τ) b' e') c c' κ) :
    LiftLaw N τ B pt M A ∧ ∀ ip, IP ip → ZetaLaw N τ B pt M A ip := by
  have hJ := GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hN hM hR.s₂ hR.s₁ hR.gr
  obtain ⟨hU, hD, hLn⟩ := h3.1 t al be ga de hd
  have hT := (GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers X _ _ _ _ _ _ (h1.1 t al be ga de hd) hU hD hLn).2
  have hPL := GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw _ _ _ _ _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).2 (isGK_fock _ _ _ _).1 (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd.1).2 _)
    (h.ds _ _ _ hN.par).1 hT
  refine ⟨GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hN hM hR.s₂ hR.s₁ hJ hPL, fun ip hip => ?_⟩
  obtain ⟨m, hm⟩ := hm
  obtain ⟨K, Θ, hF, hL1, -⟩ := hR.l2 ip hip
  have hC : Coef (X.fock _ _ _ _) A pt ip κ (phiFr (M.fr τ) b e) m K := GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rank_pos hd.1).1 (M.fr_unit τ) (M.fr_gram τ) hM.ord.1 hm hR.s₁ hL1 hF
  refine GlobalTheory.T.zetaIntegral_model_of_cover _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h1.1 t al be ga de hd) ?_ hM hN.ord.1 hm hC fun Φ hΦ => ((hJ Φ).1 hΦ).symm
  intro v hv
  obtain ⟨-, -, hgap⟩ := hd.2
  have hq7 : Formalism.MainNotions.SchurIrreducible.admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have hds2 := GlobalTheory.SphJet.lowest_type_positive_and_decays X h.ds h.hc hq7 GlobalTheory.InducedPBW.pbw_induced
  have hds3 := GlobalTheory.T.discreteSeries_integrableCoefficient_projector X hds2 (GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X)
  refine (hds3 _ _ _ hM.par _ hgap ?_ v hv).1
  unfold Formalism.MainNotions.SchurIrreducible.rangeOfSeventhSum
  rw [show al.length + be.length + (ga.length + de.length) = al.length + be.length + ga.length + de.length by omega]

theorem tie_small (h : Good D X) (hd : HypA t al be ga de) (M : DSModel V S) (τ : D.what₂.Tau) (b j : Bool)
    (hS : S τ = parOf b j (al ++ be) (ga ++ de) c) :
    (∃ m : ℤ, (m : ℚ) = 2 * c) ∧ ∃ e u, KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b j e u := by
  have hl := (GlobalTheory.LowestTypes.lowest_types t al be ga de hd).2.1
  obtain ⟨-, hn, -⟩ := hd
  exact exists_ktie h M τ (p := al.length + be.length) (q := ga.length + de.length) b j (by omega) (by simp) (by simp) hl hS

theorem tie_large (h : Good D X) (hd : HypA t al be ga de) (M : DSModel V S) (τ : D.what₂.Tau) (b j : Bool)
    (hS : S τ = parOf b j (al ++ block t ++ de) (ga ++ be) c) :
    ∃ e u, KTie (X.ds _ _ (lamA' t al be ga de)) M τ (lamA' t al be ga de) c b j e u := by
  have hl := (GlobalTheory.LowestTypes.lowest_types t al be ga de hd).2.2.1
  obtain ⟨ht, -⟩ := hd
  exact (exists_ktie h M τ (p := al.length + de.length + t) (q := ga.length + be.length) b j (by omega)
    (by simp [block]; omega) (by simp) hl hS).2

theorem noLowerTarget {T : HSp D} {p q r s : ℕ} {lam : Ix p q → ℚ} {aT : ℚ} {pS pT : SPar}
    (hS : ∀ {P} (M : DSModel V P), P τ = pS → ∃ e u, KTie (X.ds p q lam) M τ lam aT true true e u)
    (hT : ∀ {P} (M : DSModel T P), P τ = pT → ∃ e : Ix r s ≃ Fin T.rank, SignCompat (M.ε τ) e)
    (hno : ∀ i, 1 ≤ i → i ≤ r → i ≤ s → PairNo (fockAct1 p q (r - i) (s - i)) (X.ds p q lam)) :
    NoLowerTarget τ V T aT pS pT := by
  intro PS PT MS MT hPS hPT T' i hi hW ψ θ χS χT ω hω hχT sT BS BT f hf
  obtain ⟨e, u, hu⟩ := hS MS hPS
  obtain ⟨e₀, he₀⟩ := hT MT hPT
  obtain ⟨εT, fT⟩ := frame_of_adapted hf.onT
  obtain ⟨hir, his, e', he'⟩ := GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower D T T' i τ (MT.fr τ) (MT.ε τ) BT⁻¹ εT r s e₀ hW (MT.fr_gram τ)
    (MT.fr_unit τ) fT.2.1 fT.1 he₀
  obtain ⟨aS, haS⟩ := GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent D θ χS _ τ hf.inf hω.hecS hω.resS
  obtain ⟨κ, hR⟩ := exists_real hω haS hχT (isFrameOf_model MS τ) fT hf hu.ord.1 he'
  exact GlobalTheory.T.noThetaMap_models_of_noPairing_covers _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hR.s₁ (hno i hi hir his)

theorem noLowerSource {T : HSp D} {p q r s : ℕ} {lam : Ix r s → ℚ} {aS : ℚ} {pS pT : SPar}
    (hS : ∀ {P} (M : DSModel V P), P τ = pS → ∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e)
    (hT : ∀ {P} (M : DSModel T P), P τ = pT → ∃ e u, KTie (X.ds r s lam) M τ lam aS false true e u)
    (hno : ∀ i, 1 ≤ i → i ≤ p → i ≤ q → PairNo (fockAct2 (p - i) (q - i) r s) (X.ds r s lam)) :
    NoLowerSource τ V T aS pS pT := by
  intro PS PT MS MT hPS hPT S' i hi hW ψ θ χS χT ω hω hχS sS BS BT f hf
  obtain ⟨e', u, hu⟩ := hT MT hPT
  obtain ⟨e₀, he₀⟩ := hS MS hPS
  obtain ⟨εS, fS⟩ := frame_of_adapted hf.onS
  obtain ⟨hip, hiq, e, he⟩ := GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower D V S' i τ (MS.fr τ) (MS.ε τ) BS⁻¹ εS p q e₀ hW (MS.fr_gram τ)
    (MS.fr_unit τ) fS.2.1 fS.1 he₀
  obtain ⟨aT, haT⟩ := GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent D θ χT _ τ hf.inf hω.hecT hω.resT
  obtain ⟨κ, hR⟩ := exists_real hω hχS haT fS (isFrameOf_model MT τ) hf he hu.ord.1
  exact GlobalTheory.T.noThetaMap_models_of_noPairing_covers _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hR.s₂ (hno i hi hip hiq)

theorem pairNo_small (h : Good D X) (hd : HypA t al be ga de) (i : ℕ) (hi : 1 ≤ i) (h1 : i ≤ al.length + de.length + t)
    (h2 : i ≤ ga.length + be.length) :
    PairNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (X.ds _ _ (lamA al be ga de)) := by
  have hT := (GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers X h.ds h.hc t al be ga de hd i hi).1 h1 h2
  exact GlobalTheory.T.no_invariant_theta_pairing_of_no_tensor_intertwiner _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).1 (isGK_fock _ _ _ _).2 (GlobalTheory.T.fockOperators_lie_representation_commute _ _ _ _).2.2.2
    (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd).1 _) hT

theorem pairNo_large (h : Good D X) (hd : HypA t al be ga de) (hf : ∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|)
    (i : ℕ) (hi : 1 ≤ i) (h1 : i ≤ al.length + be.length) (h2 : i ≤ ga.length + de.length) :
    PairNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (X.ds _ _ (lamA' t al be ga de)) := by
  have hT := (GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers X h.ds h.hc t al be ga de hd i hi).2 hf h1 h2
  exact GlobalTheory.T.no_invariant_theta_pairing_of_no_tensor_intertwiner _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).2 (isGK_fock _ _ _ _).1
    (fun Y Z => ((GlobalTheory.T.fockOperators_lie_representation_commute _ _ _ _).2.2.2 Z Y).symm) (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd).2 _) hT

theorem PairNo.swap {p q r s : ℕ} {T : GrpData r s} {R : DSRep T} (h : PairNo (fockAct2 p q r s) R) :
    PairNo (fockAct1 r s p q) R := by
  intro U _ _ B hB
  have key := h U (B ∘ₗ (swp (Ix p q) (Ix r s)).toLinearMap) (by
    intro Z hZ P v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, swp_apply, GlobalTheory.FockSwap.rename_fockAct2]
    exact hB Z hZ _ v)
  refine LinearMap.ext fun P => ?_
  have := LinearMap.congr_fun key ((swp (Ix p q) (Ix r s)).symm P)
  simpa using this

end Core

variable {X : ProvA}

theorem chainLower (h : Good D X) : ChainLower D := by
  intro k τ V W
  obtain ⟨al, be, ga, de, ⟨hA, hF, -⟩, h1, h2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
  refine ⟨noLowerTarget (fun M hM => ?_) (fun M hM => ?_) (fun i hi hr hs => pairNo_small h hA i hi hr hs),
    noLowerSource (fun M hM => ?_) (fun M hM => ?_) (fun i hi hp hq => pairNo_large h hA hF i hi hp hq)⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ true true (hM.trans h1)
    exact ⟨e, u, hu⟩
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ false false (hM.trans h2)
    exact ⟨e, hu.ord.1⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ true false (by rw [hM, parB, ← parA, h1]; rfl)
    exact ⟨e, hu.ord.1⟩
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ false true (by rw [hM, parB, ← parA, h2]; rfl)
    exact ⟨e, u, hu⟩

theorem pairLower (h : Good D X) : PairLower D := by
  intro i τ
  obtain ⟨al, de, ⟨hA, hF, -⟩, h1, h2⟩ := GlobalTheory.T.definiteSource_pair_centred_block_parameters D i τ
  refine noLowerTarget (fun M hM => ?_) (fun M hM => ?_)
    (fun j hj hr hs => PairNo.swap (pairNo_large h hA hF j hj hr hs))
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ true true (hM.trans h2)
    exact ⟨e, u, hu⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ false false (hM.trans h1)
    exact ⟨e, hu.ord.1⟩

theorem chainTop (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hg : NodeGap D) : ChainTop D := by
  intro k τ V W
  obtain ⟨al, be, ga, de, ⟨hA, -, hG⟩, e1, e2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
  have hd : Formalism.MainNotions.SchurIrreducible.DataAR D.R.t al be ga de := ⟨hA, hG hg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨-, e, u, hu⟩ := tie_small h hA MS τ true true (hPS.trans e1)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false false (hPT.trans e2)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact lift_up h h1 h3 hd hu hu' hR
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨hm, e, u, hu⟩ := tie_small h hA MS τ true false (by rw [hPS, parB, ← parA, e1]; rfl)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false true (by rw [hPT, parB, ← parA, e2]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu hu' hR).1
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf μ 𝓕 hμ h𝓕
    obtain ⟨hm, e, u, hu⟩ := tie_small h hA MS τ true false (by rw [hPS, parB, ← parA, e1]; rfl)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false true (by rw [hPT, parB, ← parA, e2]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu hu' hR).2 _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩

theorem pairTop (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hg : NodeGap D) : PairTop D := by
  intro i τ
  obtain ⟨al, de, ⟨hA, -, hG⟩, e1, e2⟩ := GlobalTheory.T.definiteSource_pair_centred_block_parameters D i τ
  have hd : Formalism.MainNotions.SchurIrreducible.DataAR D.R.t al [] [] de := ⟨hA, hG hg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true true (hPS.trans e2)
    obtain ⟨hm, e', u', hu'⟩ := tie_small h hA MT τ false false (hPT.trans e1)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu' hu hR.swap).1
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true false (by rw [hPS, e2]; rfl)
    obtain ⟨-, e', u', hu'⟩ := tie_small h hA MT τ false true (by rw [hPT, e1]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact lift_up h h1 h3 hd hu' hu hR.swap
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf μ 𝓕 hμ h𝓕
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true true (hPS.trans e2)
    obtain ⟨hm, e', u', hu'⟩ := tie_small h hA MT τ false false (hPT.trans e1)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu' hu hR.swap).2 _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩

theorem alS_eq (k : Fin D.R.m) (τ : D.what₂.Tau) : alS D k τ = GlobalTheory.Chain.expS D k τ := by
  unfold alS GlobalTheory.Chain.expS
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h.add_one, if_pos h]
  · rw [if_neg (Nat.not_odd_iff_even.mpr h.add_one), if_neg (Nat.not_even_iff_odd.mpr h)]
    ring

theorem alT_eq (k : Fin D.R.m) (τ : D.what₂.Tau) : alT D k τ = GlobalTheory.Chain.expT D k τ := by
  unfold alT GlobalTheory.Chain.expT
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h.add_one, if_pos h]
    ring
  · rw [if_neg (Nat.not_odd_iff_even.mpr h.add_one), if_neg (Nat.not_even_iff_odd.mpr h)]

theorem itLaw (hP : GlobalTheory.Chain.ItPair D) (hL : GlobalTheory.Chain.ItLine D) (hg : NodeGap D) : ItLaw D := by
  intro k V W P P' M M' hPe hPe' ψ θ χS χT ω hω hχ f hf
  subst hPe hPe'
  have hθ : IsInfFam θ := fun ρ => (hf ρ).inf ρ
  have hC : GlobalTheory.Chain.ChainPar D k := by
    intro τ
    obtain ⟨al, be, ga, de, ⟨hA, hF, hG⟩, h1, h2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
    refine ⟨al, be, ga, de, ⟨hA, hG hg⟩, hF, ?_, ?_⟩
    · rw [h1, alT_eq]
    · rw [h2, alS_eq]
  have hW : GlobalTheory.Chain.IsStepWeil k ψ V W ω := ⟨χS, χT, hω, fun τ => by rw [← alS_eq, ← alT_eq]; exact hχ τ⟩
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    have hc : Fintype.card D.what₂.Tau = D.R.f := D.what₂.10
    have h8 : 2 ≤ D.R.m := D.R.8
    have h12 : D.R.m ≤ 2 * D.R.ord := D.R.12
    rw [← Fintype.card_pos_iff, hc]
    unfold Ranks.f Ranks.n
    omega
  have hV : GlobalTheory.Chain.IsVacVec ψ θ M M' f := ⟨(hf τ₀).theta, (hf τ₀).ne, fun τ => (hf τ).vac⟩
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hC
  exact ⟨It, hIt ω f hW hV, fun It' h' => hL k V W M M' θ ψ hθ hC ω f hW hV It It' (hIt ω f hW hV) h'⟩

theorem ioLaw (h1 : IoEx D) (h2 : IoUniq D) (h3 : IoHarm D) : IoLaw D := by
  intro i P P' M M' hP hP' ψ θ χS χT ω hω hχ c hc hpr BV f hf
  subst hP hP'
  have hθ : IsInfFam θ := fun ρ => (hf ρ).inf ρ
  obtain ⟨io, hio⟩ := h1 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf
  exact ⟨io, hio, fun io' h' => h2 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf io io' hio h',
    h3 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf io hio⟩

theorem archOnRecord_of_cover (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) (D : D7)
    (X : ProvA) (hX : GlobalTheory.Chain.RealIt.ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) :
    ArchOnRecord D := by
  obtain ⟨Y, hpar, hds, hq5, hy1, -, hy3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hDS hHC
  have hG : Good D Y := ⟨hpar, hds, hq5, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
  exact ⟨⟨chainLower hG, pairLower hG⟩, fun hg => ⟨chainTop hG hy1 hy3 hg, pairTop hG hy1 hy3 hg,
    itLaw (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D) (GlobalTheory.T.realThetaIntertwiners_proportional_of_harishChandra hDS hHC D) hg,
    ioLaw (GlobalTheory.T.lowestKTypeFockMap_exists_of_discreteSeries hDS hHC D) (GlobalTheory.T.lowestKTypeFockMap_unique_of_discreteSeries hDS hHC D) (GlobalTheory.T.lowestKTypeFockMap_harmonic_of_discreteSeries hDS hHC D)⟩⟩

theorem archOnRecord (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) (D : D7) :
    ArchOnRecord D := by
  obtain ⟨X, hpar, -, -, h1, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hDS hHC
  exact archOnRecord_of_cover hDS hHC D X hpar h1 h3

end GlobalTheory.ArchRec

end
