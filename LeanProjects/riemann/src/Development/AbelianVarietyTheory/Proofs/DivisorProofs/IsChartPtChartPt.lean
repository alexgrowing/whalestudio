import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

variable {K : Type} [Field K]

abbrev baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B] : K →+* B :=
  (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))

def transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) : Sp (DualNumber B) ⟶ A.left :=
  if h : ∃ w, IsTransl φ x v w then h.choose else spMap (algebraMap B (DualNumber B)) ≫ x

theorem isTransl_transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) : IsTransl φ x v (transl φ x v) := by
  have h : ∃ w, IsTransl φ x v w := exists_isTransl φ x hx v
  rw [transl, dif_pos h]
  exact h.choose_spec

def dlogAt {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) : B :=
  (valR (transl φ x v) Wo g.val).snd * valR x Wo g⁻¹.val

def chartVal {A : Over (Sp K)} [GrpObj A] {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (f : Γ(Z, Ω)) : B :=
  valR (x ≫ m) Ω f + algebraMap (DualNumber K) B DualNumber.eps *
    (valR (x ≫ m) Ω (δ f) + ∑ a, (∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g) *
      (valR (transl (baseMap K B) x (u a) ≫ m) Ω f).snd)

def IsChartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) {Z : Scheme.{0}} (m : A.left ⟶ Z)
    (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (l : Sp B ⟶ A'.left) : Prop :=
  l ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧ ⊤ ≤ (l ≫ m') ⁻¹ᵁ Ω ∧
    ∀ f, valR (l ≫ m') Ω f = chartVal m Ω δ u θ Wo g x f

def chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) {Z : Scheme.{0}}
    (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) : Sp B ⟶ A'.left :=
  if h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l then h.choose else x ≫ i

theorem isChartPt_chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left)
    {Z : Scheme.{0}} (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ}
    (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
    (h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l) :
    IsChartPt A' m m' Ω δ u θ Wo g x (chartPt A' i m m' Ω δ u θ Wo g x) := by
  rw [chartPt, dif_pos h]
  exact h.choose_spec

theorem valR_eq_ev {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (f : Γ(Z, U)) : valR z U f = ev z U h f := by
  rw [valR, dif_pos h]
  rfl

theorem IsChartPt.unique {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z}
    (hm' : IsPullback m' A'.hom h y1) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ}
    {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ}
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l l' : Sp B ⟶ A'.left}
    (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l) (hl' : IsChartPt A' m m' Ω.1 δ u θ Wo g x l') : l = l' := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  have e : ev (l ≫ m') Ω.1 h2 = ev (l' ≫ m') Ω.1 h2' := by
    ext f
    rw [← valR_eq_ev, ← valR_eq_ev, h3 f, h3' f]
  have e2 : l ≫ m' = l' ≫ m' := by
    rw [← GlobalTheory.FlagMod.spMap_ev (l ≫ m') Ω.2 h2, ← GlobalTheory.FlagMod.spMap_ev (l' ≫ m') Ω.2 h2', e]
  exact hm'.hom_ext e2 (h1.trans h1'.symm)

end GlobalTheory.CechKS

end
