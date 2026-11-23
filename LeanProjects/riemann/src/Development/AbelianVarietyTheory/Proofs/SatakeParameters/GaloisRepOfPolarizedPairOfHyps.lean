import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOfStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

namespace GlobalTheory.GalBridge

theorem galoisRepOfPolarizedPair_of_polarizedGaloisRep :
    LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → IrreducibleAdmissibleGL →
      StandardFunctorsFiniteLength → PolarizedGaloisRepPublished → GaloisRepOfPolarizedPair := by
  intro h1 h2 h3 h4 h5 H
  have hU : RecUnique := GlobalTheory.T.reciprocity_unique_of h1 h2 h3 h4 h5
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp
  obtain ⟨r, wt, HT, P⟩ := H E Ω l ι a ha π χ hr hp
  obtain ⟨n, hn⟩ := GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair E a ha π χ hr hp
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨art, hart, hL⟩ :=
    (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1
      (maximalRealSubfield E) Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hL l ι χ n hn
  have hμ' : IsLAdicCharOf ι χ μ := ⟨hμc, art, n, hart, hn, hμ⟩
  have hcont : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) :=
    Units.continuous_val.comp P.cont
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := by
    intro τ u o
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  refine ⟨r, wt, HT, ?_⟩
  exact
    { cont := P.cont
      ss := P.ss
      pol := ⟨μ, hμ', P.pol μ hμ'⟩
      away := fun w hl A h rc hrc σ hσ => by
        rw [← P.away w hl A h rc (hU.isTheRec_of_isRec hrc) σ hσ]
        exact isWDOf_wdOf (h := h) hl ι hcont
      pure := fun w hl A h => ⟨wdOf h hl ι r, isWDOf_wdOf (h := h) hl ι hcont, P.pure w hl A h⟩
      weights := fun τ => P.weights τ _ (hasInfChar_infChar_of_commute E a hcap (CG.mk π) (ι.toRingHom.comp τ))
      weights_conj := P.weights_conj
      above := fun Pr AI hT w A h O _ _ _ Bw hj =>
        let Q := P.above Pr AI hT w A h O Bw hj
        { deRham := Q.deRham
          jumps := Q.jumps
          iwahori := fun σ hσ hI =>
            ⟨(Q.iwahori σ hσ hI).1, fun rc hrc => (Q.iwahori σ hσ hI).2 rc (hU.isTheRec_of_isRec hrc)⟩
          crys := Q.crys } }

end GlobalTheory.GalBridge

end
