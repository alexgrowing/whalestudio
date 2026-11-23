import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

def LamEq {S : Scheme.{0}} {X Y A B : Over S} [GrpObj A] [GrpObj B] (L : LB A.left) (f₁ : X ⟶ A) (f₂ : Y ⟶ A)
    (M : LB B.left) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) : Prop :=
  LBIso (cubeLB A ![fst X Y ≫ f₁, snd X Y ≫ f₂] L) (cubeLB B ![fst X Y ≫ g₁, snd X Y ≫ g₂] M)

def WeilEq {S : Scheme.{0}} {X Y A B : Over S} [GrpObj X] [GrpObj Y] [GrpObj A] [GrpObj B] (L : LB A.left)
    (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (M : LB B.left) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) {k : Type} [Field k] (t : Sp k ⟶ S) : Prop :=
  ∀ (n : ℕ) (x : Over.mk t ⟶ X) (y : Over.mk t ⟶ Y) (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
    (Out.WeilIs A L n (x ≫ f₁) (y ≫ f₂) (unitOn c) ↔ Out.WeilIs B M n (x ≫ g₁) (y ≫ g₂) (unitOn c))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev OK (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ {H.w0}

def wK (H : Host E) : OK H := ⟨H.w0, Algebra.subset_adjoin rfl⟩

structure Ell (H : Host E) (R : Type) [CommRing R] (ω : R) where
  P : Out.PolAV (Sp R)
  dim : P.g = 1
  act : OAct (OK H) P.A
  v : epsR R ⟶ P.A
  basis : IsLieBasis ![v]
  eig : IsLieComb ![ω] ![v] (v ≫ act.act (wK H))
  adj : ∀ a b : OK H, (b : 𝓞 E) = H.bar a → LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act b)
  prim : LBIso P.L (cubeLB P.A ![𝟙 P.A, act.act (wK H)] P.L)

instance {H : Host E} {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) : IsCommMonObj C.P.A := C.P.isAb.comm

structure PAT (H : Host E) (S : Scheme.{0}) where
  t : SAB H S
  ab : IsAbelianScheme t.G
  g : ℕ
  dim : SmoothOfRelativeDimension g t.G.hom
  sym : Out.Sym t.G t.PP.L
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

abbrev PAT.pol {H : Host E} {S : Scheme.{0}} (T : PAT H S) : Out.PolAV S where
  A := T.t.G
  isAb := T.ab
  g := T.g
  smoothDim := T.dim
  L := T.t.PP.L
  isLB := T.t.PP.isLB
  rigid := ⟨T.t.PP.rig, T.t.PP.rigGen⟩
  sym := T.sym
  ample := T.ample
  ktriv := T.ktriv

def HasType (H : Host E) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G) (ρ : R)
    (p q : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (β : R →+* k), Function.Injective β → ∀ τ : 𝓞 E →+* k,
    (τ H.rt = β ρ → LieMult act (spMap β) τ p) ∧ (τ H.rt ≠ β ρ → LieMult act (spMap β) τ q)

def IsKForm {H : Host E} (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) : Prop :=
  ∀ x y, ((h x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0

structure IsTen {H : Host E} {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H)
    (T : PAT H (Sp R)) where
  ten : Serre.IsTensor T.t.G (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) C.P.A C.act D.La
  lin : ∀ (s : 𝓞 E) a, ten.tmul (s • a) = ten.tmul a ≫ T.t.act.act s
  lam : ∀ a b, LamEq T.t.PP.L (ten.tmul a) (ten.tmul b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A)

variable {K : Type} [Field K] [NumberField K]

structure GenFib (P : Out.PolAV (Sp (𝓞 K))) where
  P₀ : Out.PolAV (Sp K)
  φ : P₀.A.left ⟶ P.A.left
  fib : IsPolFibre (algebraMap (𝓞 K) K) P P₀ φ
  v : Fin P₀.g → (epsR K ⟶ P₀.A)
  basis : IsLieBasis v

namespace GenFib

variable {P P' : Out.PolAV (Sp (𝓞 K))}

def IsCoord (F : GenFib P) (u : epsR (𝓞 K) ⟶ P.A) (c : Fin F.P₀.g → K) : Prop :=
  IsTangent u ∧ ∃ w, IsVecOver (algebraMap (𝓞 K) K) F.φ u w ∧ IsLieComb c F.v w

def lieLat (F : GenFib P) : Submodule (𝓞 K) (Fin F.P₀.g → K) := Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c}

def eigLat (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K) :
    Submodule (𝓞 K) (Fin F.P₀.g → K) :=
  Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a)}

def IsHerm (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
    (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin F.P₀.g → Fin Q.g → ℂ),
    IsPolFibre s F.P₀ Q ψ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
    ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)

def IsDiffOf (F : GenFib P) (F' : GenFib P') (f : P.A ⟶ P'.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) : Prop :=
  ∀ u c, F.IsCoord u c → F'.IsCoord (u ≫ f) (M c)

end GenFib

def Splits (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] : Prop :=
  Nat.card (𝓞 E →+* 𝓞 K) = Module.finrank ℚ E

structure CMObj (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) where
  split : Splits E K
  ρ_sq : ρ ^ 2 = -(H.d : 𝓞 K)
  A : Bool → PAT H (Sp (𝓞 K))
  B : PAT H (Sp (𝓞 K))
  typeP : HasType H (A true).t.act ρ 1 0
  typeM : HasType H (A false).t.act ρ 0 1
  typeB : HasType H B.t.act ρ p q
  hh : Fin p ⊕ Fin q → 𝓞 E
  φ : ∀ j : Fin p ⊕ Fin q, (A j.isLeft).t.G ⟶ B.t.G
  lin : ∀ j, Serre.IsLinearHom (A j.isLeft).t.act B.t.act (φ j)
  onto : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ B.t.G,
    ∃ x : ∀ j : Fin p ⊕ Fin q, Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (A j.isLeft).t.G,
      y = (List.ofFn fun i : Fin (p + q) => x (finSumFinEquiv.symm i) ≫ φ (finSumFinEquiv.symm i)).prod
  weil : ∀ j, WeilEq B.t.PP.L (φ j) (φ j) (A j.isLeft).t.PP.L ((A j.isLeft).t.act.act (hh j)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

end GlobalTheory.CM
end
