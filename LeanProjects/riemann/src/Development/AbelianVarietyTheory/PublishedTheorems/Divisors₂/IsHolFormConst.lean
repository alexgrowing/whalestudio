import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable (F : Type) [Field F] [NumberField F]

abbrev FracId : Type := (FractionalIdeal (𝓞 F)⁰ F)ˣ

variable {F}

abbrev FracId.elt (𝔠 : FracId F) : Submodule (𝓞 F) F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F)

def IsTotPos (x : F) : Prop := ∀ τ : F →+* ℝ, 0 < τ x

def HasGen {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : L.Gen, t.IsGen

variable (F) in

structure Obj (𝔠 : FracId F) (S : Scheme.{0}) where

  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom

  rm : OAct (𝓞 F) A

  P : 𝔠.elt → LB (G2 A).left
  isLB : ∀ c, (P c).IsLB
  rig₁ : ∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)
  rig₂ : ∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)

  symm : ∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)

  add : ∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))

  smul : ∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)

  pos : ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)

  ker : ∀ (c : 𝔠.elt) (T : Over S) (x : T ⟶ A),
    HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1

attribute [instance] Obj.grp Obj.comm

namespace Obj

variable {𝔠 : FracId F} {S S' : Scheme.{0}}

def diag (X : Obj F 𝔠 S) (c : 𝔠.elt) : LB X.A.left := (X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left

structure IsPullBy (X' : Obj F 𝔠 S') (X : Obj F 𝔠 S) (b : S' ⟶ S) (φ : X'.A.left ⟶ X.A.left) : Prop where
  grp : IsGrpPullback X'.A X.A b φ
  act : ∀ a, (X'.rm.act a).left ≫ φ = φ ≫ (X.rm.act a).left
  pol : ∃ φ₂ : (G2 X'.A).left ⟶ (G2 X.A).left, IsSquare φ φ₂ ∧ ∀ c, LBIso (X'.P c) ((X.P c).pull φ₂)

structure Level (X : Obj F 𝔠 S) (N : ℕ) where

  pt : Fin 2 → (𝟙_ (Over S) ⟶ X.A)
  tors : ∀ i, pt i ^ N = 1
  inj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (a b : 𝓞 F),
    (toUnit (Over.mk t) ≫ pt 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ pt 1 ≫ X.rm.act b) = 1 →
      (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b
  surj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S) (y : Over.mk t ⟶ X.A), y ^ N = 1 →
    ∃ a b : 𝓞 F, y = (toUnit (Over.mk t) ≫ pt 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ pt 1 ≫ X.rm.act b)

def IsLevelPull {N : ℕ} {X' : Obj F 𝔠 S'} (α' : X'.Level N) {X : Obj F 𝔠 S} (α : X.Level N) (b : S' ⟶ S) : Prop :=
  ∃ φ, X'.IsPullBy X b φ ∧ ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left

variable {R R' : Type} [CommRing R] [CommRing R']

abbrev Lie (X : Obj F 𝔠 (Sp R)) : Type := Serre.Lie X.rm

@[reducible] def lieModule (X : Obj F 𝔠 (Sp R)) : Module (R ⊗[ℤ] 𝓞 F) X.Lie :=
  TensorProduct.Algebra.module

def IsRapoport (X : Obj F 𝔠 (Sp R)) : Prop :=
  letI := X.lieModule
  Module.Invertible (R ⊗[ℤ] 𝓞 F) X.Lie

def rapLocus (X : Obj F 𝔠 S) : Set S :=
  {s | ∀ (K : Type) [Field K] (t : Sp K ⟶ S), s ∈ Set.range t →
    ∀ (Y : Obj F 𝔠 (Sp K)) (φ : Y.A.left ⟶ X.A.left), Y.IsPullBy X t φ → Y.IsRapoport}

abbrev DetOmega (X : Obj F 𝔠 (Sp R)) : Type := X.Lie [⋀^Fin (Module.finrank ℚ F)]→ₗ[R] R

def DetGen (X : Obj F 𝔠 (Sp R)) : Type := {δ : X.DetOmega // Submodule.span R {δ} = ⊤}

def LieCorr {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} (σ : R →+* R') (φ : X'.A.left ⟶ X.A.left)
    (v : X.Lie) (v' : X'.Lie) : Prop :=
  v'.hom.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.hom.left

def DetCorr {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} (σ : R →+* R') (φ : X'.A.left ⟶ X.A.left)
    (δ : X.DetOmega) (δ' : X'.DetOmega) : Prop :=
  ∀ v v', (∀ i, LieCorr σ φ (v i) (v' i)) → δ' v' = σ (δ v)

end Obj

abbrev ObjClass (𝔠 : FracId F) : Type 1 := ∀ (R : Type) [CommRing R], Obj F 𝔠 (Sp R) → Prop

def trivialObjectCondition (𝔠 : FracId F) : ObjClass 𝔠 := fun _ _ _ ↦ True

def rapObj (𝔠 : FracId F) : ObjClass 𝔠 := fun _ _ X ↦ X.IsRapoport

@[ext] structure Rule {𝔠 : FracId F} (Q : ObjClass 𝔠) (R₀ : Type) [CommRing R₀] (k : ℕ) where

  val : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), Q R X → X.DetGen → R
  homog : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : Q R X) (δ δ' : X.DetGen) (c : R),
    δ'.1 = c • δ.1 → c ^ k * val R X hX δ' = val R X hX δ
  baseChange : ∀ (R R' : Type) [CommRing R] [Algebra R₀ R] [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R')
    (X : Obj F 𝔠 (Sp R)) (hX : Q R X) (X' : Obj F 𝔠 (Sp R')) (hX' : Q R' X') (φ : X'.A.left ⟶ X.A.left)
    (δ : X.DetGen) (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
    Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → val R' X' hX' δ' = σ (val R X hX δ)

namespace Rule

variable {𝔠 : FracId F} {Q Q' : ObjClass 𝔠} {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {k l : ℕ}

def const (Q : ObjClass 𝔠) (r : R₀) : Rule Q R₀ 0 where
  val R _ _ _ _ _ := algebraMap R₀ R r
  homog := by intros; simp
  baseChange := by intros; simp

def mul (r : Rule Q R₀ k) (s : Rule Q R₀ l) : Rule Q R₀ (k + l) where
  val R _ _ X hX δ := r.val R X hX δ * s.val R X hX δ
  homog R _ _ X hX δ δ' c h := by
    rw [← r.homog R X hX δ δ' c h, ← s.homog R X hX δ δ' c h]; ring
  baseChange R R' _ _ _ _ σ X hX X' hX' φ δ δ' h h' := by
    rw [map_mul, r.baseChange R R' σ X hX X' hX' φ δ δ' h h', s.baseChange R R' σ X hX X' hX' φ δ δ' h h']

def restrict (r : Rule Q R₀ k) (h : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), Q' R X → Q R X) :
    Rule Q' R₀ k where
  val R _ _ X hX δ := r.val R X (h R X hX) δ
  homog R _ _ X hX := r.homog R X (h R X hX)
  baseChange R R' _ _ _ _ σ X hX X' hX' := r.baseChange R R' σ X (h R X hX) X' (h R' X' hX')

def extend (r : Rule Q R₀ k) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] : Rule Q R₁ k where
  val R _ _ X hX δ :=
    letI : Algebra R₀ R := ((algebraMap R₁ R).comp (algebraMap R₀ R₁)).toAlgebra
    r.val R X hX δ
  homog R _ _ X hX δ δ' c h :=
    letI : Algebra R₀ R := ((algebraMap R₁ R).comp (algebraMap R₀ R₁)).toAlgebra
    r.homog R X hX δ δ' c h
  baseChange R R' _ _ _ _ σ X hX X' hX' φ δ δ' h h' :=
    letI : Algebra R₀ R := ((algebraMap R₁ R).comp (algebraMap R₀ R₁)).toAlgebra
    letI : Algebra R₀ R' := ((algebraMap R₁ R').comp (algebraMap R₀ R₁)).toAlgebra
    r.baseChange R R' { (σ : R →+* R') with commutes' := fun x ↦ σ.commutes (algebraMap R₀ R₁ x) }
      X hX X' hX' φ δ δ' h h'

end Rule

variable (F) in

def halfSpace : Set ((F →+* ℝ) → ℂ) := {z | ∀ τ, 0 < (z τ).im}

def dualLat (𝔞 : FracId F) : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)

def InModularGroup (𝔞 𝔟 : FracId F) (a b c d : F) : Prop :=
  a * d - b * c = 1 ∧ ∀ β ∈ 𝔟.elt, ∀ m ∈ dualLat 𝔞, β * a + m * c ∈ 𝔟.elt ∧ β * b + m * d ∈ dualLat 𝔞

def IsHolForm (𝔞 𝔟 : FracId F) (k : ℕ) (g : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ g (halfSpace F) ∧
    ∀ a b c d : F, InModularGroup 𝔞 𝔟 a b c d → ∀ z ∈ halfSpace F,
      g (fun τ ↦ ((τ a : ℂ) * z τ + (τ b : ℂ)) / ((τ c : ℂ) * z τ + (τ d : ℂ))) =
        (∏ τ, ((τ c : ℂ) * z τ + (τ d : ℂ))) ^ k * g z

def qPower (ξ : F) (z : (F →+* ℝ) → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (τ ξ : ℂ) * z τ)

def HasFourier (𝔞 𝔟 : FracId F) (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ) : Prop :=
  ∀ z ∈ halfSpace F, HasSum (fun ξ : (𝔞 * 𝔟).elt ↦ a ξ * qPower (ξ : F) z) (g z)

theorem isHolForm_const (𝔞 𝔟 : FracId F) (x : ℂ) : IsHolForm 𝔞 𝔟 0 (fun _ ↦ x) :=
  ⟨differentiableOn_const x, fun _ _ _ _ _ _ _ ↦ by simp⟩

def IsTorusPoint (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega) : Prop :=
  ∃ (c : (𝔞 * 𝔟⁻¹).elt) (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)), IsTotPos (c : F) ∧
    (∀ w, w ∈ u.Λ ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
      w = fun i ↦ 2 * Real.pi * Complex.I * ((e i m : ℂ) + (e i β : ℂ) * z (e i))) ∧
    (∀ (a : 𝓞 F) w, u.ex (fun i ↦ (e i (a : F) : ℂ) * w i) = u.ex w ≫ X.rm.act a) ∧
    (∃ χ, u.IsAH (Matrix.diagonal fun i ↦ ((2 * e i (c : F) / (4 * Real.pi ^ 2 * (z (e i)).im) : ℝ) : ℂ)) χ) ∧
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ i, u.IsDiff (W i) (v i).hom) →
      δ v = ((Real.sqrt |(discr F : ℝ)| *
        (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℝ) : ℝ) : ℂ) * W.det

def Rule.HasValues (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) {Q : ObjClass (𝔞 * 𝔟⁻¹)}
    {R₀ : Subring ℂ} {k : ℕ} (r : Rule Q R₀ k) (g : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  ∀ z ∈ halfSpace F, ∀ (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (hX : Q ℂ X) (δ : X.DetGen),
    IsTorusPoint e 𝔞 𝔟 z X δ.1 → r.val ℂ X hX δ = g z

end GlobalTheory.RealMult
