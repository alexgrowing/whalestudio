import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

namespace GlobalTheory.ShFam.GalCarry

theorem divIso_divOf_of_locRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (n n' : Letter Dw → ℤ), TriEqn C → T.LocRel C C' φ ψ t₀ → C.Y.dim = C'.Y.dim → (∀ z, n' (T.letter z) = n z) → DivIso (divOf C n') (divOf C' n) φ ψ (prodPow t₀ n) := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ _ e C C' φ ψ t₀ n n' hTri hLoc hdim hn
  obtain ⟨h1, h2, h3⟩ := hLoc
  have hsum : ∀ {Y : Var F} (D : Letter Dw → Y.Dv) (m : Letter Dw → ℤ) (y : Y.X)
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), (∀ z : Letter Dw, (D z).IsEqn y (t z.1 z.2)) →
      (∑ z, m z • D z).IsEqn y (prodPow t m) := by
    intro Y D m y t h
    classical
    have key : ∀ s : Finset (Letter Dw), (∑ z ∈ s, m z • D z).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ m z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CartierDiv.isEqn_zero y
      | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((h z).zsmul _).add ih
    exact key Finset.univ
  refine ⟨?_, h2, hdim, fun y g hg => ?_⟩
  · rw [← C'.π_str, ← C.π_str, ← Category.assoc, h1, Category.assoc, reassoc_of% T.g_str]
  obtain ⟨χ', f', t', htri', heq'⟩ := C'.gr_spec (φ.hom y)
  obtain ⟨a, χ, f, t, -, -, -, htri, ht, -⟩ := h3 y (φ.hom y) χ' f' t' rfl htri'
  have hE := hTri y χ f t htri
  have hP : (divOf C n').IsEqn y (prodPow t n') := hsum _ n' y t fun z => hE z.1 z.2
  have hP' : (divOf C' n).IsEqn (φ.hom y) (prodPow t' n) := hsum _ n (φ.hom y) t' fun z => heq' z.1 z.2
  have hprod : prodPow t n' = Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (prodPow t' n) * prodPow t₀ n := by
    simp only [prodPow]
    rw [← T.letter.prod_comp]
    simp only [map_prod, map_zpow, ← Finset.prod_mul_distrib, ← mul_zpow]
    refine Finset.prod_congr rfl fun z _ => ?_
    obtain ⟨τ, i⟩ := z
    rw [hn]
    exact congrArg (· ^ n ⟨τ, i⟩) (ht τ i)
  have hU := unitAt_map h2 (hP'.iff_unitAt.1 hg)
  refine hP.iff_unitAt.2 ?_
  convert hU using 1
  rw [hprod]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_div₀]
  exact mul_div_mul_right _ _ (Units.ne_zero _)

end GlobalTheory.ShFam.GalCarry
