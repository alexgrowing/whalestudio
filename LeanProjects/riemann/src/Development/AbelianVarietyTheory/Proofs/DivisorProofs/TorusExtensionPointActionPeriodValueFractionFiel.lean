import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem act_val_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  intro R _ _ D₀ D' pr h F _ _ y y₀ g g' hg hg' ha χ u hu z J hJ
  have hsurj : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap _
  have hflat : Flat (jFK (R := R) F) := (inferInstance : Flat (spMap (algebraMap (FractionRing R) F)))
  have hb : g.b.left = jFK (R := R) F ≫ ptK (D'.c y) := by
    rw [hg.1]
    have e : toUnit (TF (R := R) F) = (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) ≫ toUnit (TK R) :=
      toUnit_unique _ _
    show (toUnit (TF (R := R) F) ≫ D'.c y).left = _
    rw [e, Category.assoc, Over.comp_left]
    rfl

  have step1 : ∀ (z' : (TF (R := R) F).left) (J' : _), Good (JN D' D₀) z' J' →
      val (D₀.tau y₀ χ) (jFK (R := R) F) z' (rr J') =
        val (D'.tau y (h χ)) (jFK (R := R) F) z' (rl J') * val u (jFK (R := R) F ≫ ptK (D'.c y)) z' J' := by
    intro z' J' hJ'
    have g₀ := (isPart_inr D'.P.L D₀.P.L).good hJ'
    have g₁ := (isPart_inl D'.P.L D₀.P.L).good hJ'
    have e := ha.2 χ u hu z' J' hJ'
    rw [val_corr g₀ (hg'.2 χ), val_corr g₁ (hg.2 (h χ)), val_pull g₀, val_pull g₁, hb] at e
    simp only [Category.id_comp] at e
    exact e

  have p₀ := isPart_inr D'.P.L D₀.P.L
  have p₁ := isPart_inl D'.P.L D₀.P.L
  let t₀ := p₀.gen (D₀.tau y₀ χ)
  let t₂ := LB.mulGen (JN D' D₀) _ _ _ _ (p₁.gen (D'.tau y (h χ))) (LB.pullGen (JN D' D₀) _ _ u (ptK (D'.c y)))
  have key := GlobalTheory.Balanced.val_descend (jn_isLB D' D₀) t₀ t₂ (jFK (R := R) F) (fun z' J' hJ' => by
    rw [p₀.val_gen _ _ _ hJ', val_mul hJ', p₁.val_gen _ _ _ hJ', val_pull hJ']
    exact step1 z' J' hJ') z J hJ
  rw [p₀.val_gen _ _ _ hJ, val_mul hJ, p₁.val_gen _ _ _ hJ, val_pull hJ, Category.id_comp] at key
  exact key

end GlobalTheory.Mum.Two

end
