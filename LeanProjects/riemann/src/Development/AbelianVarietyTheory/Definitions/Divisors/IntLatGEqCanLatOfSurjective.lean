import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCanLat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CanExtM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {V : X.Opens}

def IsIntClass (c : GlobalTheory.LogDR.Chart t V) (c₀ : primDR c.A) : Prop :=
  ∃ (B : Over (Sp Γ(X, c.U.1))) (_ : GrpObj B) (φB : B.left ⟶ t.G.left) (q : c.A.left ⟶ B.left)
    (m : GrpMor (dp0 Γ(X, c.U.1)) (𝟙 _) B (dp0 c.S) (𝟙 _) c.A (algebraMap Γ(X, c.U.1) c.S)
      (spMap (algebraMap Γ(X, c.U.1) c.S)) q) (c₁ : primDR B),
    IsGrpPullback B t.G (chart c.U) φB ∧ q ≫ φB = c.φ ∧ m.pull c₁ = c₀

def intLatG {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : GlobalTheory.LogDR.Chart t V) : Submodule Γ(X, c.U.1) (HdR c.A) :=
  Submodule.span Γ(X, c.U.1) {h | h ∈ canSet s c ∧
    ∀ c₀, IsIntClass c c₀ → h c₀ ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)}

def intLat {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : GlobalTheory.LogDR.Chart t V) : Submodule Γ(X, c.U.1) (HdR c.A) :=
  Submodule.span Γ(X, c.U.1) {h | h ∈ canSet s c ∧
    ∀ ψ : LinearMap.BilinForm c.S (HdR c.A), IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ →
      ∀ w ∈ intLatG s c, ψ h w ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)}

section API

variable {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : GlobalTheory.LogDR.Chart t V)

def rangeSub : Submodule Γ(X, c.U.1) c.S where
  carrier := Set.range (algebraMap Γ(X, c.U.1) c.S)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ a b⟩
  smul_mem' := by rintro r _ ⟨a, rfl⟩; exact ⟨r * a, by rw [map_mul, Algebra.smul_def]⟩

theorem mem_rangeSub {x : c.S} : x ∈ rangeSub c ↔ x ∈ Set.range (algebraMap Γ(X, c.U.1) c.S) := Iff.rfl

theorem mem_intLatG_of {h : HdR c.A} (hh : h ∈ canSet s c)
    (hi : ∀ c₀, IsIntClass c c₀ → h c₀ ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)) : h ∈ intLatG s c :=
  Submodule.subset_span ⟨hh, hi⟩

theorem mem_intLat_of {h : HdR c.A} (hh : h ∈ canSet s c)
    (hi : ∀ ψ : LinearMap.BilinForm c.S (HdR c.A), IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ →
      ∀ w ∈ intLatG s c, ψ h w ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)) : h ∈ intLat s c :=
  Submodule.subset_span ⟨hh, hi⟩

theorem intLatG_apply_mem {h : HdR c.A} (hh : h ∈ intLatG s c) {c₀ : primDR c.A} (hc : IsIntClass c c₀) :
    h c₀ ∈ Set.range (algebraMap Γ(X, c.U.1) c.S) := by
  induction hh using Submodule.span_induction with
  | mem x hx => exact hx.2 c₀ hc
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => exact (rangeSub c).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul c.S r x, LinearMap.smul_apply, smul_eq_mul]
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by rw [map_mul, ha]⟩

theorem intLat_pair_mem {h : HdR c.A} (hh : h ∈ intLat s c) {ψ : LinearMap.BilinForm c.S (HdR c.A)}
    (hψ : IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ) {w : HdR c.A} (hw : w ∈ intLatG s c) :
    ψ h w ∈ Set.range (algebraMap Γ(X, c.U.1) c.S) := by
  induction hh using Submodule.span_induction with
  | mem x hx => exact hx.2 ψ hψ w hw
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact (rangeSub c).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul c.S r x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by rw [map_mul, ha]⟩

theorem intLatG_le_canLat : intLatG s c ≤ canLat s c := Submodule.span_mono fun _ hh => hh.1

theorem intLat_le_canLat' : intLat s c ≤ canLat s c := Submodule.span_mono fun _ hh => hh.1

theorem intLatG_eq_canLat_of_surjective (hs : Function.Surjective (algebraMap Γ(X, c.U.1) c.S)) :
    intLatG s c = canLat s c :=
  le_antisymm (intLatG_le_canLat s c) (Submodule.span_mono fun _ hh => ⟨hh, fun _ _ => hs _⟩)

theorem intLat_eq_canLat_of_surjective' (hs : Function.Surjective (algebraMap Γ(X, c.U.1) c.S)) :
    intLat s c = canLat s c :=
  le_antisymm (intLat_le_canLat' s c) (Submodule.span_mono fun _ hh => ⟨hh, fun _ _ _ _ => hs _⟩)

end API

end GlobalTheory.CanExtM

section Examples

open GlobalTheory.CanExtM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {V : X.Opens}
  {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : GlobalTheory.LogDR.Chart t V)

example : (0 : HdR c.A) ∈ intLat s c := Submodule.zero_mem _

example (hs : Function.Surjective (algebraMap Γ(X, c.U.1) c.S)) : intLat s c = intLatG s c :=
  (intLat_eq_canLat_of_surjective' s c hs).trans (intLatG_eq_canLat_of_surjective s c hs).symm

example (ψ : LinearMap.BilinForm c.S (HdR c.A)) (w : HdR c.A) : ψ 0 w = algebraMap Γ(X, c.U.1) c.S 0 := by simp

end Examples
