import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

variable {k : Type} [CommRing k] {X : Scheme.{0}}

def sheet {p : X ⟶ Sp k} {σ : k →+* ℂ} (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (y : CxPts p σ) : CxPts t τ :=
  ⟨y.1, specZIsTerminal.hom_ext _ _⟩

def emb (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) : k →+* ℂ :=
  (Spec.preimage (y.1 ≫ p)).hom

def unsheet (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) : CxPts p (emb p y) :=
  ⟨y.1, (Spec.map_preimage (y.1 ≫ p)).symm⟩

def WOver {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} {B : LB X} (φ : ∀ σ : k →+* ℂ, Weight p σ B)
    (ψ : Weight t τ B) : Prop :=
  ∀ (σ : k →+* ℂ) (i : B.ι) (y : CxPts p σ), y ∈ ptsIn p σ (B.U i) → ψ.φ i (sheet t τ y) = (φ σ).φ i y

def wZ {p : X ⟶ Sp k} (L : HermLB p) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) : Weight t τ L.B where
  isLB := L.isLB
  φ i y := (L.φ (emb p y)).φ i (unsheet p y)
  trans i j y hi hj := (L.φ (emb p y)).trans i j (unsheet p y) hi hj

def toZ {p : X ⟶ Sp k} (L : HermLB p) (t : X ⟶ Sp ℤ) (hc : ∀ τ, (wZ L t τ).IsCInf) : HermLB t where
  B := L.B
  isLB := L.isLB
  φ τ := wZ L t τ
  cInf := hc
  conj _ _ i y y' h hy := L.conj _ _ i (unsheet p y) (unsheet p y') h hy

theorem emb_sheet {p : X ⟶ Sp k} {σ : k →+* ℂ} (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (y : CxPts p σ) :
    emb p (sheet t τ y) = σ := by
  have h : y.1 ≫ p = Spec.map (CommRingCat.ofHom σ) := y.2
  show (Spec.preimage (y.1 ≫ p)).hom = σ
  rw [h, Spec.preimage_map]
  rfl

theorem sheet_unsheet (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) :
    sheet t τ (unsheet p y) = y := rfl

theorem wOver_wZ {p : X ⟶ Sp k} (L : HermLB p) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) : WOver L.φ (wZ L t τ) := by
  intro σ i y _
  have key : ∀ (σ' : k →+* ℂ) (_ : σ' = σ) (y' : CxPts p σ'), y'.1 = y.1 → (L.φ σ').φ i y' = (L.φ σ).φ i y := by
    rintro σ' rfl y' h
    rw [Subtype.ext h]
  exact key _ (emb_sheet t τ y) _ rfl

end GlobalTheory.CompanionTheory.Ar.BaseZ
