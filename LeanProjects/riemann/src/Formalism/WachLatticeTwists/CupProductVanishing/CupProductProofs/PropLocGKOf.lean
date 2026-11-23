import Formalism.WachLatticeTwists.CupProductVanishing.Statement
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocContBK

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem compat : StatCompat := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hc a t
  have h : D.pr (D.q a) t = D.inv (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (KO O)) (toKO O) toKO_cont
      (toKO_equiv D.ε) (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT' a (D.j' t))) := by
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction t using Submodule.Quotient.induction_on with
      | H t => rfl
  rw [h, hc]
  rfl

theorem realise_of (hI : StatInvGK) : StatRealise := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hK hO hF hD
  obtain ⟨inv, invF, h⟩ := hI p K O hK hO hF D.ε hD.cyc
  exact ⟨inv.toLinearMap, invF.toLinearMap,
    ⟨hD.cyc, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩, inv.bijective, invF.bijective, h⟩

theorem propLocGK_of (h1 : StatFinGK) (h2 : StatRatGK) (h3 : StatIntGK) : StatPropLocGK := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q hK hO hF hD hi hiF hc hBK hsat hP hQ
  exact propLocContBK O (GK p K) VT VT' D HfV HfV' (pairF D) ℓ e' ι₁ ι₂ P Q hD.lat hD.perf
    (h1 p K O VT VT' D hK hO hD) hc hBK hsat (h2 p K O VT VT' D hK hO hF hD hiF)
    (compat O (GK p K) VT VT' D hc) (h3 p K O VT VT' D hK hO hF hD hi) hP hQ

end Formalism.RepresentationBoundsCohomology.T2
