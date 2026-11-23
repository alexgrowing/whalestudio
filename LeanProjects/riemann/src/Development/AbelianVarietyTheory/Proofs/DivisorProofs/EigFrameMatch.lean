import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.EigParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Generic

variable {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) (χ : 𝓞 E → R)

def IsBasG {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ (∀ i (a : 𝓞 E), u i ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ u i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x u a w

end Generic

variable {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem comb_iff {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (a : Fin n → R) (w : epsAt x ⟶ t.G) :
    IsCombAt x a v w ↔ IsCombAtG t x (fun i => (v i).left) a w.left :=
  exists_congr fun _ => and_congr Iff.rfl ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h.symm⟩

theorem basis_iff (χ : 𝓞 E →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) :
    IsEigBasisAt t.act x χ v ↔ IsBasG t x χ (fun i => (v i).left) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨Over.w (v i), (h1 i).1⟩, fun i a => (h1 i).2 a, fun w hw he => ?_⟩
    let w' : epsAt x ⟶ t.G := Over.homMk w hw.1
    exact (existsUnique_congr fun a => comb_iff v a w').1 (h2 w' ⟨hw.2, he⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨(h1 i).2, h2 i⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => comb_iff v a w).2 (h3 w.left ⟨Over.w w, hw.1⟩ hw.2)

theorem exists_over (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : IsBasG t x χ u) :
    ∃ v : Fin n → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => Over.homMk (u i) (hu.1 i).1, (basis_iff χ _).2 hu, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem exists_left (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) :
    ∃ u : Fin m → (Sp (DualNumber R) ⟶ t.G.left), IsBasG t x χ u ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => (v i).left, (basis_iff χ _).1 hv, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem eigFrame_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (V : Set (gen Y)) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y), x ≫ genStr Y = spMap j → Set.range x ⊆ V → ∀ f : EigFrame Y j (x ≫ genι Y), (∃ v w, FrY Y V τ j x v w ∧ Match τ f v w) ∧ ∀ v w, FrY Y V τ j x v w → ∃ f' : EigFrame Y j (x ≫ genι Y), Match τ f' v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ hτ V R _ j x hx hV f
  have hp : D.mult τ = D.p := GlobalTheory.Harm.mult_of_mem D hτ
  have hq : D.mult (conjEmb τ) = D.q := GlobalTheory.Harm.mult_conjEmb_of_mem D hτ
  have hne : conjEmb τ ≠ τ := fun e => (GlobalTheory.Harm.not_mem_hostType_iff H τ).2 (by rw [e]; exact hτ) hτ
  have hf : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (f.v σ) :=
    fun σ => ⟨f.tan σ, f.eig σ, f.basis σ⟩
  refine ⟨?_, fun v w h => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_over _ hp (hf τ)
    obtain ⟨w, hw, hw'⟩ := exists_over _ hq (hf (conjEmb τ))
    refine ⟨v, w, ⟨hx, hV, hv, ?_⟩, hv', hw'⟩
    rw [comp_chi_bar]
    exact hw
  · obtain ⟨-, -, hv, hw⟩ := h
    rw [comp_chi] at hv
    rw [comp_chi_bar] at hw
    obtain ⟨v₁, a, a'⟩ := exists_left _ hp hv
    obtain ⟨w₁, b, b'⟩ := exists_left _ hq hw
    classical
    let g := Function.update (Function.update f.v τ v₁) (conjEmb τ) w₁
    have g1 : g τ = v₁ := by
      simp only [g, Function.update_of_ne hne.symm, Function.update_self]
    have g2 : g (conjEmb τ) = w₁ := Function.update_self _ _ _
    have hg : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (g σ) := fun σ => by
      by_cases e2 : σ = conjEmb τ
      · rw [e2, g2]; exact b
      by_cases e1 : σ = τ
      · rw [e1, g1]; exact a
      have : g σ = f.v σ := by simp only [g, Function.update_of_ne e2, Function.update_of_ne e1]
      rw [this]; exact hf σ
    refine ⟨⟨g, fun σ => (hg σ).1, fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩, fun i k e => ?_, fun i k e => ?_⟩
    · exact (a' i k e).trans (congrFun g1 k).symm
    · exact (b' i k e).trans (congrFun g2 k).symm

end GlobalTheory.DetLine.EigParts
