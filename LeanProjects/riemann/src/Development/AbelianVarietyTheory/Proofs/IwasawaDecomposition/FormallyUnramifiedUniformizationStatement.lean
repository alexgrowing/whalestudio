import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X)
    (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
    ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ →
    Module.Projective (𝓞 E) P.D.toPre.X ∧ Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  first | exact @GlobalTheory.ChartCharRank.projective_and_finrank_le_min | exact GlobalTheory.ChartCharRank.projective_and_finrank_le_min | (intros; apply GlobalTheory.ChartCharRank.projective_and_finrank_le_min <;> assumption)
