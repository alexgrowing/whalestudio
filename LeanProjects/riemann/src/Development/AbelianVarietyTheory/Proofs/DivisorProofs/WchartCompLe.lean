import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section

namespace GlobalTheory.HomFixMat

abbrev powPull {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => a)

theorem wchart_comp_le {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f ≫ φ) j ≤ f ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j := by
  intro y hy
  exact Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    simpa using this

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev topS (Rg : Type) [CommRing Rg] : Over (Sp Rg) := overRes (T := baseOver (Sp Rg)) ⊤

def coord {X : Scheme.{0}} {N : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (n : Fin N) : Γ(X, ⊤) :=
  g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.X n))

def matOf {X : Scheme.{0}} {mA mB : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Fin mA → Fin mB → Γ(X, ⊤) :=
  fun i j => coord g (finProdFinEquiv (i, j))

abbrev affπ (Rg : Type) [CommRing Rg] (N : ℕ) : Sp (MvPolynomial (Fin N) Rg) ⟶ Sp Rg :=
  Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))

variable (A B L M) in

def IsTest {T : Scheme.{0}} (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') : Prop :=
  IsGrpPullback A' A t φA' ∧ IsGrpPullback B' B t φB' ∧ IsMonHom Φ' ∧
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left)

def IsPullD {T₁ T₂ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left)
    (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left)
    (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (h : T₂ ⟶ T₁) : Prop :=
  ∃ (ψA : A₂.left ⟶ A₁.left) (ψB : B₂.left ⟶ B₁.left), IsGrpPullback A₂ A₁ h ψA ∧
    IsGrpPullback B₂ B₁ h ψB ∧ ψA ≫ φA₁ = φA₂ ∧ ψB ≫ φB₁ = φB₂ ∧ Φ₂.left ≫ ψB = ψA ≫ Φ₁.left

variable (A L) in

def IsBCBasis (k : ℕ) {m : ℕ} (b : Fin m → LB.Sec (LPow A L (k : ℤ) (topS Rg))) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (topS Rg).left)
    (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))),
    (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) →
    LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧
    Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev isoLB (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)} (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) : LB A'.left :=
  LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
    (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))

abbrev zeroPt {R : Type} [CommRing R] (A' : Over (Sp R)) [GrpObj A'] : Sp R ⟶ A'.left := η[A'].left

variable (L M) in

def IsMat (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A']
    [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) : Prop :=
  ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)),
    ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ α.IsGen ∧
    (∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k) ∧
    ∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

variable (L M) in

def Hyps (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) : Prop :=
  IsAbelianScheme A ∧ IsAbelianScheme B ∧ L.IsLB ∧ M.IsLB ∧ eA.IsGen ∧ eB.IsGen ∧ RelAmple A L ∧ 1 ≤ k ∧
    VeryAmpleAt B M k ∧ IsBCBasis A L k bA ∧ IsBCBasis B M k bB

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat
variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

theorem IsPullD.comp {T₁ T₂ T₃ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] {φA₁ : A₁.left ⟶ A.left}
    {φB₁ : B₁.left ⟶ B.left} {Φ₁ : A₁ ⟶ B₁} {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] {φA₂ : A₂.left ⟶ A.left}
    {φB₂ : B₂.left ⟶ B.left} {Φ₂ : A₂ ⟶ B₂} {A₃ B₃ : Over T₃} [GrpObj A₃] [GrpObj B₃] {φA₃ : A₃.left ⟶ A.left}
    {φB₃ : B₃.left ⟶ B.left} {Φ₃ : A₃ ⟶ B₃} {h₁ : T₂ ⟶ T₁} {h₂ : T₃ ⟶ T₂}
    (p₁ : IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h₁) (p₂ : IsPullD φA₂ φB₂ Φ₂ φA₃ φB₃ Φ₃ h₂) :
    IsPullD φA₁ φB₁ Φ₁ φA₃ φB₃ Φ₃ (h₂ ≫ h₁) := by
  obtain ⟨ψA, ψB, qA, qB, eA, eB, eΦ⟩ := p₁
  obtain ⟨ψA', ψB', qA', qB', eA', eB', eΦ'⟩ := p₂
  refine ⟨ψA' ≫ ψA, ψB' ≫ ψB, qA'.comp qA, qB'.comp qB, by rw [Category.assoc, eA, eA'],
    by rw [Category.assoc, eB, eB'], ?_⟩
  rw [← Category.assoc, eΦ', Category.assoc, eΦ, Category.assoc]

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem hom_ext_affine (Rg : Type) [CommRing Rg] (N : ℕ) (X : Scheme.{0}) (g g' : X ⟶ Sp (MvPolynomial (Fin N) Rg))
    (h0 : g ≫ affπ Rg N = g' ≫ affπ Rg N) (h1 : ∀ n, coord g n = coord g' n) : g = g' := by
  apply ext_of_isAffine
  refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))) _ _).1 ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have e := congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)) h0
    simp only [Scheme.Hom.comp_appTop] at e
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg N).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
    rw [n2]
    simpa using e
  · intro n
    exact h1 n

end GlobalTheory.HomFixMat
