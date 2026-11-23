import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameTri

theorem tri_trans : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} (f : EigFrame Z φ x) (g : EigFrame Z φ' x') (k : EigFrame Z φ'' x'') (ψ : R →+* R') (χ : R' →+* R'') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) (s : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R''ˣ), f.Tri ψ g t → g.Tri χ k s → f.Tri (χ.comp ψ) k (fun τ i => Units.map χ.toMonoidHom (t τ i) * s τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z R R' R'' _ _ _ φ φ' φ'' x x' x'' f g k ψ χ t s hf hg
  have hx : x'' = spMap (χ.comp ψ) ≫ x := by rw [hg.1, hf.1, ← Category.assoc, spMap_comp_spMap]
  have hφ : φ'' = (χ.comp ψ).comp φ := by rw [hg.2.1, hf.2.1, RingHom.comp_assoc]
  refine ⟨hx, hφ, fun τ i => ?_⟩
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨f'', hf''⟩ := f'.exists_isMap χ hg.2.1 hg.1
  obtain ⟨g'', hg''⟩ := g.exists_isMap χ hg.2.1 hg.1
  obtain ⟨hA, hAd⟩ := EigFrame.Tri.co τ hf hf'
  obtain ⟨hB, hBd⟩ := EigFrame.Tri.co τ hg hg''
  have hM : f''.co g'' τ = (f'.co g τ).map χ := EigFrame.IsMap.co τ hf'' hg'' hg.1
  have hQ : f''.co k τ = f''.co g'' τ * g''.co k τ := (f''.co_mul g'' k τ).symm
  have hd : ∀ a j, j < a → (f'.co g τ).map χ a j = 0 := fun a j h => by
    rw [Matrix.map_apply, hA a j h, map_zero]
  refine ⟨fun a => f''.co k τ a i, ?_, fun a ha => ?_, ?_⟩
  · dsimp only
    rw [hQ, hM, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.map_apply, hAd, hBd]; simp
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hd i j h, zero_mul]
      · rw [hB j i h, mul_zero]
    · simp
  · dsimp only
    rw [hQ, hM, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hd a j h, zero_mul]
    · rw [hB j i (lt_of_lt_of_le ha h), mul_zero]
  · have e : (fun j => spMap (dualMap (χ.comp ψ)) ≫ f.v τ j) = f''.v τ := funext fun j => by
      rw [hf'' τ j, hf' τ j, ← Category.assoc]
      congr 1
      have e2 : dualMap (χ.comp ψ) = (dualMap χ).comp (dualMap ψ) := by
        ext r <;> simp [dualMap]
      rw [e2]
      simp [spMap, Spec.map_comp]
    rw [e]
    exact f''.co_spec k τ i

end GlobalTheory.FrameTri
