import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HalfGeo.GensProof

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

def prodChar {O : Type} [CommRing O] {x : Sp O ⟶ X} {q N : ℕ} (c : Fin N → TorsChar t x q) (n : Fin N → ℕ) :
    TorsChar t x q where
  χ B _ _ _ w := ∏ m, (c m).χ B w ^ n m
  mul B _ _ _ w w' hw hw' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun m _ => by rw [(c m).mul B w w' hw hw', _root_.mul_pow]
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    rw [Units.coe_prod, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun m _ => by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (c m).nat B B' φ g g' hg hg']

theorem gens : GensSt := by
  intro E _ _ _ H X _ t K _ _ ξ q hq hζ hs R _ _ _ _ _ _ x hx p _ ψ z hψ hz N χ ch hχ hch c'
  obtain ⟨-, h⟩ := GlobalTheory.HtChar.induced_chars E H X t K ξ q hq hζ hs R x hx
  obtain ⟨-, h2, h3⟩ := h p ψ z hψ hz
  obtain ⟨χ', hχ'⟩ := h2 c'
  obtain ⟨n, rfl⟩ := hχ χ'
  refine ⟨n, h3 _ c' (prodChar ch n) hχ' fun σ k a w hσ hk hw ha => ?_⟩
  have hr : ∀ m, ∃ b : R, algebraMap R K b = ((χ m k : Kˣ) : K) := fun m => GlobalTheory.HtChar.root_mem hq
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, GlobalTheory.HtChar.ker_pow, map_one, Units.val_one])
  choose b hb using hr
  obtain rfl : a = ∏ m, b m ^ n m := IsFractionRing.injective R K (by
    rw [ha, map_prod, MonoidHom.finset_prod_apply, Units.coe_prod]
    exact Finset.prod_congr rfl fun m _ => by rw [map_pow, hb, MonoidHom.pow_apply, Units.val_pow_eq_pow_val])
  show ((∏ m, (ch m).χ _ w ^ n m : (↥(intO ℂ_[p]))ˣ) : ↥(intO ℂ_[p])) = _
  rw [map_prod, Units.coe_prod]
  exact Finset.prod_congr rfl fun m _ => by
    rw [map_pow, Units.val_pow_eq_pow_val, hch m σ k (b m) w hσ hk hw (hb m)]

end GlobalTheory.HalfGeo.GensProof
