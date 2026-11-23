import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderFibreAutAtLevelMoveFixedPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (x : Sp ℂ ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), Formalism.L2.Pj.IsLevMove ρ ν gM gA → x ≫ ρ = x → ∃ (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N : ℕ) (ev : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), IsMonHom θ ∧ 0 < N ∧ (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A ∧ (∀ a, act.act a ≫ θ = θ ≫ act.act a) ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act.act c) ∧ (∀ a, ev a = 1 ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (∀ c ∈ l.Mb, q ≫ act.act c = 1) → ∃ a, ev a = q) ∧ ∀ a, ev (gM a) ≫ θ = ev a := by
  first | exact @GlobalTheory.LevMoveFibre.exists_fibreAut | exact GlobalTheory.LevMoveFibre.exists_fibreAut | (intros; apply GlobalTheory.LevMoveFibre.exists_fibreAut <;> assumption)
