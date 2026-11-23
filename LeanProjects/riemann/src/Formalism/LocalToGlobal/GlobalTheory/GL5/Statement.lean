import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions
open scoped TensorProduct

def TiedRealF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i)

def FrameTied (D : D7) (Lv : LevelData D) : Prop :=
  letI := D.host.cmStar
  ∀ (u : D.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (t : Fin D.R.k → v.adicCompletion D.host.F),
    (∃ y ∈ Formalism.L2.Herm.locL (F := D.host.F) (E := D.host.E) v (Lv u).Lb,
        ∀ a, ((Lv u).splitG i v h (y a)).1 = t a) ↔
      ∀ a, ((((Lv u).frG i v h)⁻¹ : GL (Fin D.R.k) (v.adicCompletion D.host.F)) :
        Matrix (Fin D.R.k) (Fin D.R.k) (v.adicCompletion D.host.F)).mulVec t a ∈
          v.adicCompletionIntegers D.host.F

def TiedFrameF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameTied (Fm.D x i) (Fm.ex x hx i).lev

def WeilSiegelCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
      Formalism.MainNotions.StandardLattice.SW1a1 F E σ M J ∧ Formalism.MainNotions.StandardLattice.SW1a2 F E σ M J ∧ Formalism.MainNotions.StandardLattice.SW1b1 F E σ M J ∧
      Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J ∧ Formalism.MainNotions.StandardLattice.SW1c1 F E σ M J ∧ Formalism.MainNotions.StandardLattice.SW1c2 F E σ M J ∧
      Formalism.MainNotions.StandardLattice.SW1c3 F E σ M J

def WeilSiegelGauge : Prop :=
  Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWa1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWa2 ∧
  Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWb1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWb2 ∧
  Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc1 ∧ Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc2 ∧
  Formalism.MainNotions.UnusedSlot34.ForAllCM Formalism.MainNotions.UnusedSlot34.SWc3

def MassRatioStd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 3 ≤ M →
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K M) (Formalism.MainNotions.StandardLattice.stdLat K M) /
              Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K (M - 1)) (Formalism.MainNotions.StandardLattice.stdLat K (M - 1)) =
      Formalism.HermitianLatticesTheory.massRatioRightSide K M

def VolRatioTrue (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ x : W.V, W.hT x x = (if s then 1 else -1) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) ∧
        ∀ (μ : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram))
          (𝓕 : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram))
          (μ' : Measure (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram))
          (𝓕' : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram)),
          Formalism.MainNotions.StandardLattice.IsVolMeas D W P Q μ →
          IsFundamentalDomain (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
          Formalism.MainNotions.StandardLattice.IsVolMeas D W' (if s then P - 1 else P) (if s then Q else Q - 1) μ' →
          IsFundamentalDomain (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
          (μ 𝓕).toReal / (μ' 𝓕').toReal = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

def HCFormalDegree (D : D7) : Prop :=
  cdScaleTie D →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), Formalism.MainNotions.S.IsDS ε lam σ → w ≠ 0 →
      Formalism.MainNotions.S.fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

def LandherrHasse (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ b : Fin W.rank → W.V, LinearIndependent D.host.E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0

def GenusMassStd (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

def HostInputsF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x), HCFormalDegree (Fm.D x i) ∧ LandherrHasse (Fm.D x i) ∧ GenusMassStd (Fm.D x i)

def VolRatioTrueF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), VolRatioTrue (Fm.D x i)

def LinkTies : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → Formalism.MainNotions.StandardLattice.TiesF Fm

def SiegelWeilPartOneFromWeil : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), WeilSiegelCM → Formalism.MainNotions.StandardLattice.FamilyPartOne Fm

def SiegelWeilFamilyFromWeil : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), WeilSiegelGauge → Formalism.MainNotions.UnusedSlot34.KudlaFamilyStatement Fm

def Link2All : Prop := MassRatioStd → Formalism.MainNotions.StandardLattice.MassVolumeBoundsAll

def Link2 : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm →
    Formalism.MainNotions.StandardLattice.FamilyMassVolumeBounds Fm

def Link3All : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C3 : ℝ, C ≤ C3 → ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm →
    (∀ x (i : Fm.Ix x), HCFormalDegree (Fm.D x i)) → Formalism.MainNotions.StandardLattice.FamilyTheoremThreeAdmitted Fm → Formalism.MainNotions.StandardLattice.FamilyTheoremThreeGeneral Fm C3

def Link3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C3 : ℝ, C ≤ C3 → ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm →
    (∀ x (i : Fm.Ix x), HCFormalDegree (Fm.D x i)) → Formalism.MainNotions.StandardLattice.FamilyTheoremThreeAdmitted Fm → Formalism.MainNotions.StandardLattice.FamilyTheoremThree Fm C3

def Link4p : Prop := ∀ (D : D7) (Lv : LevelData D), Formalism.MainNotions.StandardLattice.Conclusion4p D Lv

def Link4 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C3 : ℝ, C ≤ C3 → ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → TiedFrameF Fm →
    MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm → Formalism.MainNotions.StandardLattice.AdmF Fm → Formalism.MainNotions.StandardLattice.FamilyPartFour Fm C3

def FamilyBoundWithConstant : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C3 : ℝ, C ≤ C3 → ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → TiedFrameF Fm →
    WeilSiegelCM → MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm → Formalism.MainNotions.StandardLattice.AdmF Fm → Formalism.MainNotions.StandardLattice.ConclusionOnFamily Fm C3

def FamilyBoundWithConstantLiteral : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ C3 : ℝ, C ≤ C3 → ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → TiedFrameF Fm →
    WeilSiegelCM → MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm → Formalism.MainNotions.StandardLattice.KudlaFamilyStatement Fm C3

def SplitTiedF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (∀ j, Formalism.MainNotions.StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧
    ∀ u, Formalism.MainNotions.StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T

def Mu0TieF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), Formalism.MainNotions.StandardLattice.Mu0Tie (Fm.D x i) u

def LinkCount5 : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → TiedFrameF Fm →
    MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm → Formalism.MainNotions.StandardLattice.AdmF Fm → Formalism.MainNotions.Lnk.CountF Fm

def LinkProviso : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), TiedRealF Fm → TiedFrameF Fm → SplitTiedF Fm → Mu0TieF Fm →
    MassRatioStd → HostInputsF Fm → VolRatioTrueF Fm → Formalism.MainNotions.StandardLattice.AdmF Fm →
      ∃ C0 : ℝ, 1 ≤ C0 ∧ Formalism.MainNotions.ChosenProviso Fm C0

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
