import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianActionPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_action_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (U Y : Scheme.{0}) (f : U ⟶ Y) (π : Y ⟶ S) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (μ : G'.left ⟶ G.left) (act : OAct (𝓞 E) G') (t₀ : SAB H U) (y : U ⟶ F.X) (α : t₀.G.left ⟶ F.univ.A.left) (α₂ : (G2 t₀.G).left ⟶ (G2 F.univ.A).left) (ψ : t₀.G.left ⟶ G'.left), SiegData g φ n F S s j G e BD d N → f ≫ π = y ≫ j → IsGrpPullback G' G π μ → IsGrpPullback t₀.G G' f ψ → ψ ≫ μ = α ≫ e → (∀ a, (t₀.act.act a).left ≫ ψ = ψ ≫ (act.act a).left) → IsGrpPullback t₀.G F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ t₀.G t₀.PP.L) (F.univ.P.pull α₂) → ∃ M : LB G'.left, M.IsLB ∧ LBIso (M.pull ψ) t₀.PP.L := by
  first | exact @GlobalTheory.SiegTripleBundle.exists_bundle | exact GlobalTheory.SiegTripleBundle.exists_bundle | (intros; apply GlobalTheory.SiegTripleBundle.exists_bundle <;> assumption)
