import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.IsGrowFormEvAt
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor

noncomputable section

namespace PositivityTheory.RgEis

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange in

def eqv : AE F E ≃+* 𝔸[E] := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).toRingEquiv

variable {F E}

def adCM (σ : E →ₐ[F] E) (χ : Chr F E) : Ad E (AE F E) where
  i := inclR (F := F) (AF F)
  σ := (cA σ).toRingHom
  O := (intAd E).comap (eqv F E).toRingHom
  W := InfinitePlace E
  φ w := ((adStd E).φ w).comp (eqv F E).toRingHom
  lg x := (adStd E).lg (Units.map (eqv F E).toRingHom.toMonoidHom x)
  χ := χ

def ForCM (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    (E →ₐ[F] E) → Chr F E → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (χ : Chr F E) (c : ℕ),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c → Q σ χ

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Continuous (eqv F E) ∧ Continuous (eqv F E).symm ∧ (∀ x : E, eqv F E (inclR (F := F) (AF F) x) = algebraMap E 𝔸[E] x) ∧
    (∀ z : AE F E, eqv F E z ∈ intAd E ↔ finOne F • z ∈ intHat F E) ∧
    (∀ x : (AE F E)ˣ, (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = absE F E x)

def DictInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    (∀ (w : InfinitePlace E) (z : AE F E), (adStd E).φ w (eqv F E (cA σ z)) = starRingEnd ℂ ((adStd E).φ w (eqv F E z))) ∧
    ∀ τ : ∀ w : InfinitePlace F, EmbOver E w,
      (∀ w, ∃ w' : InfinitePlace E, (∀ z, piInf (τ w) z = (adStd E).φ w' (eqv F E z)) ∨
        ∀ z, piInf (τ w) z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) ∧
      ∀ w' : InfinitePlace E, ∃ w, (∀ z, piInf (τ w) z = (adStd E).φ w' (eqv F E z)) ∨
        ∀ z, piInf (τ w) z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))

def CMGood : Prop := ForCM fun σ χ => (adCM σ χ).Good

def CMMir : Prop := ForCM fun σ χ => (adCM σ χ).MirGL

def SgOne : Prop := ForCM fun σ χ => ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 1 → (adCM σ χ).Sg ε ι

def SgAll : Prop := ForCM fun σ χ => ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι → (adCM σ χ).Sg ε ι

end PositivityTheory.RgEis
