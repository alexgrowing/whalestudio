import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameWeylPermutationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

theorem lands_unique (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (hstr : hV.fromSpec ≫ genStr Z = spMap φV)
    (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (ψ : Γ(gen Z, V) →+* Ω) (a : Coord Dw → Ω) (hL : Lands Φ hV f₀ w i ψ a) (x : Sp Ω ⟶ gen Z)
    (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (hg : FrameIn hV f₀ w ψ hx g a)
    (j : U.Comp) (p : Sp Ω ⟶ (Φ.C j).Y.X) (hp : p ≫ (Φ.C j).π = x) (hc : (Φ.C j).Carries p g) : j = i := by
  subst hx
  obtain ⟨g₁, hg₁, p₁, hp₁, hc₁⟩ := hL
  obtain ⟨t, ht⟩ := GlobalTheory.T.eigen_frame_weyl_permutation hV f₀ w (RingHom.id Ω) ψ rfl rfl g₁ g a hg₁ hg
  have hc₁' : (Φ.C i).Carries p₁ g := by
    obtain ⟨y, ψ', φ₁, f, t₀, t', hp', hf0, hf⟩ := hc₁
    exact ⟨y, ψ', φ₁, f, t₀, _, hp', hf0, GlobalTheory.T.eigen_frame_composition f g₁ g ψ' (RingHom.id Ω) t' t hf ht⟩
  have hs : (spMap ψ ≫ hV.fromSpec) ≫ genStr Z = spMap (ψ.comp φV) := by
    rw [Category.assoc, hstr]
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨q, _, hq⟩ := Φ.lifts Ω (ψ.comp φV) (spMap ψ ≫ hV.fromSpec) hs g
  have h1 := hq ⟨j, p⟩ ⟨hp, hc⟩
  have h2 := hq ⟨i, p₁⟩ ⟨hp₁, hc₁'⟩
  exact congrArg Sigma.fst (h1.trans h2.symm)

end GlobalTheory.ShFam.Cell
