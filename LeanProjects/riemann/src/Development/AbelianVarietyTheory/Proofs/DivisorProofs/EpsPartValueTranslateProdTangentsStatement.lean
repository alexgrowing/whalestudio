import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartValueTranslateProdTangents
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eps_part_value_translate_prod_tangents : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g → ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)), (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) → ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O), (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := by
  first | exact @GlobalTheory.EpsAdd.snd_valR_mul_prod | exact GlobalTheory.EpsAdd.snd_valR_mul_prod | (intros; apply GlobalTheory.EpsAdd.snd_valR_mul_prod <;> assumption)
