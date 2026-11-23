import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SqrtNegPrimeMemKur
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubLoc

theorem sqrtKur_holds (l : ℕ) [Fact l.Prime] : SqrtKur l := fun p hp h4 hne y hy =>
  GlobalTheory.SqrtUnram.sqrt_neg_prime_mem_Kur l p hp h4 (Ne.symm hne) y hy

theorem kw_le_Kur_all : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  intro D i hl2 hq hd w hw
  exact kw_le_Kur_of_ne i (UpperTheory.Small.not_dvd_condN D.host (D.nd.lPrime i).out hl2 hq hd) w hw

end GlobalTheory.HubLoc
