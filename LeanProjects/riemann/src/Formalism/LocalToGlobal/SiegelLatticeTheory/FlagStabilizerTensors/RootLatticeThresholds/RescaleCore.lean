import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.RescaleCore

def OmCompat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ), Formalism.L2.SG.LocVol.StdHyp σ J ψ →
    Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J →
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
      (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n →
      ∃ νX : Measure (Fin a → Fin n → AF F ⊗[F] E), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧
        ∃ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX

def SWInputs : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J ∧ Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J

def GramStdND : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ)
    (P : Frame E n r) (T : F), (∀ x, σ (σ x) = x) → IsHermND σ J → P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0

def NCovolOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∃ μN : Measure (Nsub (AF F) σ J P), μN.IsHaarMeasure ∧ covol μN = 1

def LocTieExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (r : ℕ) (P : Frame E n r) (T : F),
    Formalism.L2.SG.LocVol.StdHyp σ J ψ → P.IsStd σ J T →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (μG : Measure (HA (Fv F v) σ J)), μG.IsHaarMeasure →
      ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS

def MWRescale : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∀ (μN : Measure (Nsub (AF F) σ J P)) (μH : Measure (Hsub (AF F) σ J P))
      (μNinf : Measure (Nsub (Ainf F) σ J P)) (μHinf : Measure (Hsub (Ainf F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μN.IsHaarMeasure → μH.IsHaarMeasure → μNinf.IsHaarMeasure → μHinf.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μN = μN ∧ W.μH = μH ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μSv = μSv

end Formalism.L2.SG.Pf.RescaleCore
