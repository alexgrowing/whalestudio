import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBX

abbrev Tor {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Type := {x : 𝟙_ (Over (Sp K)) ⟶ P.A // x ^ N = 1}

def TorFull {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : K →+* Ω) (z : Over.mk (spMap f) ⟶ P.A), z ^ N = 1 →
    ∃ x : Tor P N, spMap f ≫ x.1.left = z.left

structure TGrp (R K : Type) [CommRing R] [Field K] [Algebra R K] (P : PolAV (Sp K)) (N : ℕ) : Type 1 where

  AA : Over (Sp R)
  [grp : GrpObj AA]
  [comm : IsCommMonObj AA]
  smooth : SmoothOfRelativeDimension P.g AA.hom
  sep : IsSeparated AA.hom
  qc : QuasiCompact AA.hom

  φ : P.A.left ⟶ AA.left
  fib : IsGrpPullback P.A AA (spMap (algebraMap R K)) φ

  G : Over (Sp R)
  [grpG : GrpObj G]
  [commG : IsCommMonObj G]
  semi : IsSemiAbelian G

  j : G ⟶ AA
  jhom : IsMonHom j
  jopen : IsOpenImmersion j.left

  φ₀ : P.A.left ⟶ G.left
  fac : φ₀ ≫ j.left = φ
  fib₀ : IsGrpPullback P.A G (spMap (algebraMap R K)) φ₀
  pos : 1 ≤ N
  full : TorFull P N

  τ : Tor P N → (𝟙_ (Over (Sp R)) ⟶ AA)
  τ_over : ∀ x, (x.1.left ≫ φ : Sp K ⟶ AA.left) = spMap (algebraMap R K) ≫ (τ x).left
  cover : ∀ z : AA.left, ∃ x, z ∈ Set.range ((toUnit G ≫ τ x) * j).left

attribute [instance] TGrp.grp TGrp.comm TGrp.grpG TGrp.commG

section Model

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {P : PolAV (Sp K)} {N : ℕ}

def TGrp.comp (m : TGrp R K P N) (σ : 𝟙_ (Over (Sp R)) ⟶ m.AA) : Set m.AA.left := Set.range ((toUnit m.G ≫ σ) * m.j).left

def TGrp.Lifts (m : TGrp R K P N) (x : 𝟙_ (Over (Sp K)) ⟶ P.A) (σ : 𝟙_ (Over (Sp R)) ⟶ m.AA) : Prop :=
  (x.left ≫ m.φ : Sp K ⟶ m.AA.left) = spMap (algebraMap R K) ≫ σ.left

structure TBun (m : TGrp R K P N) (n : ℕ) where

  M : RigLB m.AA
  cub : Nonempty (CubicalStr m.AA M)

  w : LB.Iso (M.L.pull m.φ) (lbPow P.L n)
  gen : w.IsGen

def Ext {P₂ : PolAV (Sp K)} {N₂ : ℕ} (m : TGrp R K P N) (m₂ : TGrp R K P₂ N₂) (a : P.A ⟶ P₂.A) (a' : m.AA ⟶ m₂.AA) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ m.φ ≫ a'.left = a.left ≫ m₂.φ

end Model

def IntAt {X Y : Scheme.{0}} {M : LB X} {φ : Y ⟶ X} {N : LB Y} (w : LB.Iso (M.pull φ) N) (s : N.Sec) (z : X) : Prop :=
  ∃ (V : X.Opens) (p : M.ι) (f : Γ(X, V)), z ∈ V ∧ V ≤ M.U p ∧
    ∀ (i : N.ι) (W : Y.Opens) (h₁ : W ≤ N.U i ⊓ (M.pull φ).U fun _ => p) (h₂ : W ≤ φ ⁻¹ᵁ V),
      resG Y (h₁.trans inf_le_left) (s.f i) =
        resG Y h₁ (@id (Γ(Y, N.U i ⊓ (M.pull φ).U fun _ => p)ˣ) (w.s (i, fun _ => p)) :
          Γ(Y, N.U i ⊓ (M.pull φ).U fun _ => p)) * (φ.appLE V W h₂).hom f

def secSmul {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) {N : LB Y} (c : K) (s : N.Sec) : N.Sec :=
  secComb p (fun _ : Unit => c) fun _ => s

def den {R K : Type} [CommRing R] [Field K] [Algebra R K] {P : PolAV (Sp K)} {N n : ℕ} {m : TGrp R K P N} (B : TBun m n)
    (s : (lbPow P.L n).Sec) (Z : Set m.AA.left) : Set K :=
  {c | ∀ z ∈ Z, IntAt B.w (secSmul P.A.hom c s) z}

section Lattice

variable {K : Type} [Field K] [NumberField K] {P : PolAV (Sp K)} {N n : ℕ} {m : TGrp (𝓞 K) K P N}

def Pres (B : TBun m n) {r : ℕ} (b : Fin r → (lbPow P.L n).Sec) (E : Submodule (𝓞 K) (Fin r → K))
    (hE : HermFam K (Fin r → K)) : Prop :=
  Function.Bijective (fun c : Fin r → K => secComb P.A.hom c b) ∧
  (∀ c, c ∈ E ↔ ∃ t : B.M.L.Sec, SecMaps B.w (secPull t m.φ) (secComb P.A.hom c b)) ∧ IsThetaMeanSquareNorm B.w b hE P.g

def HasDeg (B : TBun m n) (r : ℕ) (x : ℝ) : Prop :=
  ∃ (b : Fin r → (lbPow P.L n).Sec) (E : Submodule (𝓞 K) (Fin r → K)) (hE : HermFam K (Fin r → K)),
    Pres B b E hE ∧ Full E ∧ deg hE E = x

end Lattice

section Power

variable {S : Scheme.{0}}

def quadLB {A T : Over S} [GrpObj A] (L : LB A.left) {k : ℕ} (x : Fin k → (T ⟶ A)) (Q : Matrix (Fin k) (Fin k) ℤ) : LB T.left :=
  LB.LinComb L (K := Fin k × Fin k) (fun p => (if p.1 = p.2 then x p.1 else x p.1 * x p.2).left)
    fun p => if p.1 = p.2 then 2 * Q p.1 p.1 - ∑ j, Q p.1 j else if p.1 < p.2 then Q p.1 p.2 else 0

def IsProd {A X : Over S} [GrpObj A] [GrpObj X] {k : ℕ} (pr : Fin k → (X ⟶ A)) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ ∀ (T : Over S) (y : Fin k → (T ⟶ A)), ∃! x : T ⟶ X, ∀ u, x ≫ pr u = y u

def lin {A T : Over S} [GrpObj A] {k : ℕ} (v : Fin k → ℤ) (x : Fin k → (T ⟶ A)) : T ⟶ A :=
  (List.ofFn fun j => x j ^ v j).prod

def IsMat {A X X' : Over S} [GrpObj A] {k : ℕ} (pr : Fin k → (X ⟶ A)) (pr' : Fin k → (X' ⟶ A))
    (a : Matrix (Fin k) (Fin k) ℤ) (f : X ⟶ X') : Prop :=
  ∀ i, f ≫ pr' i = lin (a i) pr

def IsPowQ (P P' : PolAV S) {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℤ) (pr : Fin k → (P'.A ⟶ P.A)) : Prop :=
  IsProd pr ∧ P'.g = k * P.g ∧ LBIso P'.L (quadLB P.L pr Q)

end Power

def IsPowMod {R K : Type} [CommRing R] [Field K] [Algebra R K] {P P' : PolAV (Sp K)} {N : ℕ} (m : TGrp R K P N)
    (m' : TGrp R K P' N) {k : ℕ} (pr : Fin k → (P'.A ⟶ P.A)) (prA : Fin k → (m'.AA ⟶ m.AA)) : Prop :=
  IsProd prA ∧ (∀ u, Ext m' m (pr u) (prA u)) ∧
  ∀ z : m'.AA.left, z ∈ Set.range m'.j.left ↔ ∀ u, (prA u).left z ∈ Set.range m.j.left

abbrev spSub (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] {I : Type} (C : Subalgebra R (I → R)) :
    Over (Sp O) :=
  Over.mk (spMap ((algebraMap R C).comp (algebraMap O R)))

def KerDat {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R] {X : Over (Sp O)} {I : Type} [Fintype I]
    [DecidableEq I] (x : I → (𝟙_ (Over (Sp O)) ⟶ X)) (C : Subalgebra R (I → R)) (p : spSub O C ⟶ X) : Prop :=
  (∀ i, spMap ((Pi.evalRingHom (fun _ => R) i).comp C.val.toRingHom) ≫ p.left = spMap (algebraMap O R) ≫ (x i).left) ∧
  (∃ c : I → I → R, (∀ i, c i ∈ C) ∧ (Matrix.of c).det ≠ 0) ∧
  ∀ c : I → I → R, (∀ i, c i ∈ C) → (Fintype.card I : R) ^ Fintype.card I ∣ (Matrix.of c).det ^ 4

section Iso

variable {K : Type} [Field K] [NumberField K] {P₁ P₂ : PolAV (Sp K)} {N n : ℕ} {m₁ : TGrp (𝓞 K) K P₁ N}
  {m₂ : TGrp (𝓞 K) K P₂ N}

def KerH (a : P₁.A ⟶ P₂.A) (a' : m₁.AA ⟶ m₂.AA) (d : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra (𝓞 K) R] [Algebra R K]
    [IsScalarTower (𝓞 K) R K] [IsFractionRing R K],
    ∃ (x : Fin d → (𝟙_ (Over (Sp K)) ⟶ P₁.A)) (σ : Fin d → (𝟙_ (Over (Sp (𝓞 K))) ⟶ m₁.AA)) (C : Subalgebra R (Fin d → R))
      (p : spSub (𝓞 K) C ⟶ m₁.AA), Function.Injective x ∧ (∀ z, z ≫ a = 1 ↔ z ∈ Set.range x) ∧
      (∀ i, m₁.Lifts (x i) (σ i)) ∧ KerDat σ C p ∧ p ≫ a' = 1

def KerY (B₁ : TBun m₁ n) (B₂ : TBun m₂ 1) (a : P₁.A ⟶ P₂.A) (a' : m₁.AA ⟶ m₂.AA) (d : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra (𝓞 K) R] [Algebra R K]
    [IsScalarTower (𝓞 K) R K] [IsFractionRing R K],
    ∃ (y : Fin d → (𝟙_ (Over (Sp K)) ⟶ P₂.A)) (σ : Fin d → (𝟙_ (Over (Sp (𝓞 K))) ⟶ m₂.AA)) (C : Subalgebra R (Fin d → R))
      (p : spSub (𝓞 K) C ⟶ m₂.AA), Function.Injective y ∧
      (∀ z, (∃ t : Tor P₁ n, z = t.1 ≫ a) ↔ z ∈ Set.range y) ∧ (∀ i, m₂.Lifts (y i) (σ i)) ∧ KerDat σ C p ∧
      LBIso (B₂.M.L.pull ((fst (spSub (𝓞 K) C) m₁.AA ≫ p) * (snd (spSub (𝓞 K) C) m₁.AA ≫ a')).left)
        (B₁.M.L.pull (snd (spSub (𝓞 K) C) m₁.AA).left)

def Prim (B₂ : TBun m₂ 1) (a' : m₁.AA ⟶ m₂.AA) : Prop :=
  ∀ s : (lbPow P₂.L 1).Sec, (∀ t : Tor P₁ N, ∀ z ∈ m₂.comp (m₁.τ t ≫ a'), IntAt B₂.w s z) → ∀ z, IntAt B₂.w s z

def IsoDat (B₁ : TBun m₁ n) (B₂ : TBun m₂ 1) (a : P₁.A ⟶ P₂.A) (a' : m₁.AA ⟶ m₂.AA) : Prop :=
  1 ≤ n ∧ n ∣ N ∧ 2 ∣ N ∧ P₂.g = P₁.g ∧ Ext m₁ m₂ a a' ∧ LBIso (B₂.M.L.pull a'.left) B₁.M.L ∧
  (∃ (b' : m₂.AA ⟶ m₁.AA) (e : ℕ), IsMonHom b' ∧ e ≠ 0 ∧ b' ≫ a' = (𝟙 m₂.AA) ^ e) ∧
  KerH a a' (n ^ P₁.g) ∧ KerY B₁ B₂ a a' (n ^ P₁.g) ∧ Prim B₂ a'

end Iso

def Over₀ {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K''] [Algebra K K'']
    {P : PolAV (Sp K'')} {N : ℕ} (ψ : P.A.left ⟶ F.P₀.A.left) (m : TGrp (𝓞 K'') K'' P N) : Prop :=
  GlobalTheory.MBLow.IsOver F ψ m.φ₀

def slope (g n : ℕ) (x : ℝ) : ℝ := -x / 2 + (g : ℝ) / 4 * Real.log (n / (2 * Real.pi))

end GlobalTheory.MBX

end
