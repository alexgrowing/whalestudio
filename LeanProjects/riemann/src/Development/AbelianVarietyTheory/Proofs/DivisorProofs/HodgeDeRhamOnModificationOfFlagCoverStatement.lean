import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.HorFrame.exists_horizontal_lift | exact GlobalTheory.HorFrame.exists_horizontal_lift | (intros; apply GlobalTheory.HorFrame.exists_horizontal_lift <;> assumption)
