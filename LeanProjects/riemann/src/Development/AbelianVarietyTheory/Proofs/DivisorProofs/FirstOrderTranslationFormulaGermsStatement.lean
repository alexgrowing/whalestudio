import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGerms
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrder_translation_formula_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  first | exact @GlobalTheory.TranslGerm.transl_germ | exact GlobalTheory.TranslGerm.transl_germ | (intros; apply GlobalTheory.TranslGerm.transl_germ <;> assumption)
