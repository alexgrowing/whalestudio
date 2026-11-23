import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem isArchNormSq_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (σ : k' →+* ℂ) (N : ℝ), (∀ a, IsVecOver i n.φ (x a) (x' a)) → AdelicDegreeTameRamification.IsArchNormSq t x (σ.comp i) N → AdelicDegreeTameRamification.IsArchNormSq t' x' σ N := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' σ N hx ⟨t'', p, g, u, Hm, α, y, W, h₁, h₂, h₃⟩
  have key : ∀ (f : Sp ℂ ⟶ Sp k) (q : SABMap t'' t f), f = spMap σ ≫ spMap i →
      ∃ m' : SABMap t'' t' (spMap σ), q.φ = m'.φ ≫ n.φ := by
    rintro f q rfl
    exact ObjMaps.exists_sab_cancel n q
  obtain ⟨m', hm'⟩ := key _ p (spMap_comp_spMap i σ).symm
  refine ⟨t'', m', g, u, Hm, α, y, W, h₁, fun a => ?_, h₃⟩
  refine EllComp.isVecOver_cancel (f := i) (g := σ) (φ := n.φ) (ψ := m'.φ) (v := x a) n.cart.1 m'.cart.1 (hx a) ?_
  rw [← hm']
  exact h₂ a

end GlobalTheory.FlatDegreeCompare
