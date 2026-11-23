import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_extension_normal_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (t₀ : SAB H U) (φ : t₀.G.left ⟶ G'.left), IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsSemiAbelian G' → IsGrpPullback t₀.G G' (jQ ≫ pullback.fst _ _) φ → ∃ act : OAct (𝓞 E) G', ∀ a, (t₀.act.act a).left ≫ φ = φ ≫ (act.act a).left := by
  first | exact @GlobalTheory.exists_oAct_extend_dedekindModel | exact GlobalTheory.exists_oAct_extend_dedekindModel | (intros; apply GlobalTheory.exists_oAct_extend_dedekindModel <;> assumption)
