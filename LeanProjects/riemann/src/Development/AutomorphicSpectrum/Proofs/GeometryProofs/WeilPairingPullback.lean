import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapSnd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtTorPull

theorem spMap_comp_fields {A B C : Type} [Field A] [Field B] [Field C] (i : A →+* B) (τ : B →+* C) :
    spMap (τ.comp i) = spMap τ ≫ spMap i := by
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cancel_spMap {K K' : Type} [Field K] [Field K'] (τ : K →+* K') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of K) ⟶ Z) (h : spMap τ ≫ a = spMap τ ≫ b) : a = b := by
  have hd : IsSchemeTheoreticallyDominant (spMap τ) :=
    LieEx.std_of_inj (CommRingCat.ofHom τ) τ.injective
  have hs : Function.Surjective (spMap τ) := by
    intro p
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K')) := inferInstance
    exact ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact LieEx.epi_of_surj (spMap τ) hs a b h

theorem secVal_eq_of_eq {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem torsion_clause : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hD G _ _ L n e hGW hFT G' _ _ φ hP hFT' L' e' hGW' y y' hy hy' hcomp hlift hdown W s hW
    k _ _ τ xk g c h hxk hgn hWeil
  obtain ⟨x', hx⟩ := hFT' k τ g hgn
  let U : Over.mk (spMap τ ≫ ξ') ⟶ Over.mk ξ' := Over.homMk (spMap τ) rfl
  have hgU : g = U ≫ x' := Over.OverMorphism.ext hx
  have hx'n : x' ^ n = 1 := by
    have e1 : preHom (G := G') U (x' ^ n) = preHom (G := G') U 1 := by
      rw [map_pow, map_one]
      show (U ≫ x') ^ n = 1
      rw [← hgU]
      exact hgn
    apply Over.OverMorphism.ext
    apply cancel_spMap τ
    exact congrArg (fun z => z.left) e1
  obtain ⟨g₀, hg₀, hxg⟩ := hdown x' hx'n
  have hc' : (c : k) = τ (e' y' x') := (hGW'.weil y' x' hy' hx'n k τ xk g c hxk hx).1 hWeil
  have hc : (c : k) = (τ.comp i) (e y g₀) := by
    rw [hc', hcomp g₀ x' hg₀ hx'n hxg]
    rfl
  let U₀ : Over.mk (spMap (τ.comp i) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (τ.comp i)) rfl
  have hW1 : Out.WeilIs G L n (U₀ ≫ y) (U₀ ≫ g₀) (unitOn c) :=
    (hGW.weil y g₀ hy hg₀ k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c rfl rfl).2 hc
  have hg₁ : (U₀ ≫ g₀) ^ n = 1 := by
    have e1 : preHom (G := G) U₀ (g₀ ^ n) = (U₀ ≫ g₀) ^ n := map_pow _ _ _
    rw [← e1, hg₀, map_one]
  have hl : g.left ≫ φ = (U₀ ≫ g₀).left := by
    show g.left ≫ φ = spMap (τ.comp i) ≫ g₀.left
    rw [hx, Category.assoc, hxg, spMap_comp_fields, Category.assoc]
  have h' : ⊤ ≤ (g.left ≫ φ) ⁻¹ᵁ W := h
  have h₁ : ⊤ ≤ (U₀ ≫ g₀).left ⁻¹ᵁ W := hl ▸ h'
  rw [HtPull.seccomp k _ _ g.left φ W h h' s, secVal_eq_of_eq hl W h' h₁ s]
  exact hW k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c h₁ rfl hg₁ hW1

end GlobalTheory.CompanionTheory.Ar.HtTorPull
