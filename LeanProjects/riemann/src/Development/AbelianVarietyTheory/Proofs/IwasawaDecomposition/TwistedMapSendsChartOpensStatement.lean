import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedMapSendsChartOpens
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_map_sends_chart_opens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X)
    (mu : TwMap σ Z'.t Z.t π), σ H.w0 = H.w0 → ∀ (M : GlobalTheory.Reg.MChart Z) (U' : Z'.X.Opens) (hU' : IsAffineOpen U'),
    U' ≤ π ⁻¹ᵁ M.U → ∃ (v₀ : Fin M.n → (Sp (DualNumber Γ(Z'.X, U')) ⟶ Z'.t.G.left))
      (ρ : 𝓞 E → Matrix (Fin M.n) (Fin M.n) Γ(Z'.X, U')),
      ∀ (R' : Type) [CommRing R'] (f : Γ(Z'.X, U') →+* R') (t' : SAB H (Sp R'))
        (m : SABMap t' Z'.t (spMap f ≫ hU'.fromSpec)), ∃ v' : Fin M.n → (epsR R' ⟶ t'.G),
        (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧
          ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  first | exact @GlobalTheory.LiePull.lie_pull | exact GlobalTheory.LiePull.lie_pull | (intros; apply GlobalTheory.LiePull.lie_pull <;> assumption)
