import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSabExtensionGenFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_action_extends_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (semi : IsSemiAbelian G') (act : OAct (𝓞 E) G') (t₀ : SAB H U) (φ : t₀.G.left ⟶ G'.left), IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsProper t₀.G.hom → IsGrpPullback t₀.G G' (jQ ≫ pullback.fst _ _) φ → (∀ a, (t₀.act.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ M : LB G'.left, M.IsLB → LBIso (M.pull φ) t₀.PP.L → ∃ (PP : RigLB G') (cub : CubicalStr G' PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G' semi act PP cub h₁ h₂ h₃) (jQ ≫ pullback.fst _ _)), m.φ = φ := by
  first | exact @GlobalTheory.GenFibreTripleExt.exists_sab_extension_genFibre | exact GlobalTheory.GenFibreTripleExt.exists_sab_extension_genFibre | (intros; apply GlobalTheory.GenFibreTripleExt.exists_sab_extension_genFibre <;> assumption)
