import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalModelProjectiveFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_model_projective_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (π : Y ⟶ S) (t₀ : SAB H U) (y : U ⟶ F.X) (α : t₀.G.left ⟶ F.univ.A.left) (α₂ : (G2 t₀.G).left ⟶ (G2 F.univ.A).left), 3 ≤ n → SiegData g φ n F S s j G e BD d N → IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsFinite π → IsProper t₀.G.hom → jQ ≫ pullback.fst _ _ ≫ π = y ≫ j → IsGrpPullback t₀.G F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ t₀.G t₀.PP.L) (F.univ.P.pull α₂) → ∃ (t : SAB H Y) (m : SABMap t₀ t (jQ ≫ pullback.fst _ _)) (μ : t.G.left ⟶ G.left), IsGrpPullback t.G G π μ ∧ m.φ ≫ μ = α ≫ e ∧ abLocus t.G = π ⁻¹' abLocus G := by
  first | exact @GlobalTheory.SiegTripleExt.exists_sab_pull | exact GlobalTheory.SiegTripleExt.exists_sab_pull | (intros; apply GlobalTheory.SiegTripleExt.exists_sab_pull <;> assumption)
