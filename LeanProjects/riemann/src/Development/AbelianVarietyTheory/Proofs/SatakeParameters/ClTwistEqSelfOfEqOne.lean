import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
