import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TriFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {A : Type} [CommRing A] (s : X ⟶ Sp A) (ε : 𝓞 E →+* A)

def TriFrames (q : ℕ) {W Y : Scheme.{0}} (b : W ⟶ X) (a : W ⟶ Y) (n : ℕ) (L : ℕ → LB Y) : Prop :=
  ∃ (J : Type) (T : J → W.Opens) (idx : ∀ m : Fin n, J → (L m).ι)
    (vec : ∀ (j : J) (R : Type) [CommRing R] (x : Sp R ⟶ W), ⊤ ≤ x ⁻¹ᵁ T j → Fin n →
      (Sp (DualNumber R) ⟶ t.G.left)),
    (∀ w : W, ((q : ℕ) : W.residueField w) = 0 → ∃ j, w ∈ T j) ∧
    (∀ (m : Fin n) j, T j ≤ a ⁻¹ᵁ (L m).U (idx m j)) ∧
    (∀ j (R : Type) [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j) (m : Fin n),
      Formalism.L2.Pj.IsTanAtG t (x ≫ b) (vec j R x h m)) ∧
    (∀ j (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j)
      (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ T j) (m : Fin n),
      vec j R' (spMap ψ ≫ x) h' m = spMap (Formalism.L2.Pj.dualMap ψ) ≫ vec j R x h m) ∧
    (∀ j (R : Type) [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j),
      ∃ (N : ℕ) (e : Fin n ↪ Fin N) (u : Fin N → (Sp (DualNumber R) ⟶ t.G.left)),
        (∀ m, u (e m) = vec j R x h m) ∧ (∀ i, Formalism.L2.Pj.IsTanAtG t (x ≫ b) (u i)) ∧
        ∀ w, Formalism.L2.Pj.IsTanAtG t (x ≫ b) w → ∃! cf : Fin N → R, Formalism.L2.Pj.IsCombAtG t (x ≫ b) u cf w) ∧
    (∀ j (R : Type) [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j) (ψ : A →+* R), x ≫ b ≫ s = spMap ψ →
      (∀ (m : Fin n) (c : 𝓞 E), vec j R x h m ≫ (t.act.act c).left = spMap (epsMul (ψ (ε c))) ≫ vec j R x h m) ∧
      ∀ w, Formalism.L2.Pj.IsTanAtG t (x ≫ b) w →
        (∀ c : 𝓞 E, w ≫ (t.act.act c).left = spMap (epsMul (ψ (ε c))) ≫ w) →
        ∃! cf : Fin n → R, Formalism.L2.Pj.IsCombAtG t (x ≫ b) (vec j R x h) cf w) ∧
    ∀ j j' (R : Type) [CommRing R] (x : Sp R ⟶ W) (h : ⊤ ≤ x ⁻¹ᵁ T j) (h' : ⊤ ≤ x ⁻¹ᵁ T j') (m : Fin n),
      ∃ cf : Fin n → R, cf m = valR (x ≫ a) _ ((L m).g (idx m j) (idx m j')).val ∧
        (∀ m' : Fin n, m < m' → cf m' = 0) ∧
        Formalism.L2.Pj.IsCombAtG t (x ≫ b) (vec j R x h) cf (vec j' R x h' m)

end GlobalTheory.TriFlag
