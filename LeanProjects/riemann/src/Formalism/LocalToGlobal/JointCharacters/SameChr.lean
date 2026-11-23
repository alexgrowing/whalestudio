import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace Formalism.L2.JoinChr

open Formalism.L2.Theta Formalism.L2.Host

structure SameChr {D : D7} {X : ThetaX D} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : ThetaTied D X) (H : ThetaChrTied D C nch Tp X) : Prop where

  idem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e, IsPlIdem D e P

  fin : ∀ (c : X.Chr) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P →
    ∀ (k : D.host.Eˣ) (x : (AE D)ˣ), (x : AE D) = locE D e (k : D.host.E) →
      ((T.eChr c x : Circle) : ℂ) = (((H.eChr c).locK P k : ℂˣ) : ℂ)

  inf : ∀ θ, IsInfFam (D := D) θ → ∀ (c : X.Chr) (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : (AE D)ˣ),
    IsInfLoc D θ τ (k : D.host.E) (x : AE D) →
      ((T.eChr c x : Circle) : ℂ) = (((H.eChr c).locInf (plOf D θ τ) (atInf (plOf D θ τ) k) : ℂˣ) : ℂ)

end Formalism.L2.JoinChr

end
