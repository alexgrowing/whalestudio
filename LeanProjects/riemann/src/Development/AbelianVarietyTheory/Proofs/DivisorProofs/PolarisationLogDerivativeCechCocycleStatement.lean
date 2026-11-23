import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycle
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_logDerivative_cechCocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  first | exact @GlobalTheory.KappaCoc.kappa_cocycle | exact GlobalTheory.KappaCoc.kappa_cocycle | (intros; apply GlobalTheory.KappaCoc.kappa_cocycle <;> assumption)
