import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

section Algebra

abbrev abelian₂ (K : Type) [Field K] : Type := ExteriorAlgebra K Ω[K⁄ℤ]

variable {K : Type} [Field K]

abbrev dK (f : K) : Ω[K⁄ℤ] := KaehlerDifferential.D ℤ K f

variable (K) in

def extD : abelian₂ K →+ abelian₂ K := (CechDR.dDR ℤ K).toAddMonoidHom

theorem extD_apply (η : abelian₂ K) : extD K η = CechDR.dDR ℤ K η := rfl

def dlog (g : Kˣ) : Ω[K⁄ℤ] := ((g⁻¹ : Kˣ) : K) • dK (g : K)

def spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) : AddSubgroup (abelian₂ K) :=
  AddSubgroup.closure
    {η | ∃ c ∈ M, ∃ v : Fin a → Ω[K⁄ℤ], (∀ i, v i ∈ H) ∧ η = c • ExteriorAlgebra.ιMulti K a v}

def frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : Ω[K⁄ℤ] :=
  if i ∈ J then dlog (x i) else dK (x i : K)

def logWedge {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) : abelian₂ K :=
  ((I.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod

def chartForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) :=
  spanForms {c | c * t ∈ A} (Set.range (frame x J)) a

def IsCoord {n : ℕ} (x : Fin n → Kˣ) : Prop :=
  LinearIndependent K (fun i => dK (x i : K)) ∧
    Submodule.span K (Set.range fun i => dK (x i : K)) = ⊤

structure AlgChart (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) : Prop where

  mem : ∀ i, (x i : K) ∈ A

  coord : IsCoord x

  deriv : ∀ f ∈ A, ∃ c : Fin n → K, (∀ i, c i ∈ A) ∧ dK f = ∑ i, c i • dK (x i : K)

  root : ∀ (S : Finset (Fin n)) (g : K) (m : ℕ), 0 < m →
    g ^ m / ∏ j ∈ S, (x j : K) ∈ A → g / ∏ j ∈ S, (x j : K) ∈ A

def IsCartierMap (p : ℕ) {n : ℕ} (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K) : Prop :=
  (∀ c : K, γ (algebraMap K (abelian₂ K) c) = algebraMap K (abelian₂ K) (c ^ p)) ∧
    ∀ i, γ (ExteriorAlgebra.ι K (dlog (x i))) = ExteriorAlgebra.ι K (dlog (x i))

def IsEulerContraction {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K) : Prop :=
  θ 1 = 0 ∧ (∀ (v : Ω[K⁄ℤ]) (η : abelian₂ K),
    θ (ExteriorAlgebra.ι K v * η) = θ (ExteriorAlgebra.ι K v) * η - ExteriorAlgebra.ι K v * θ η) ∧
    ∀ j, θ (ExteriorAlgebra.ι K (dlog (x j))) = if j = i then 1 else 0

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

def locRing (y : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).range

theorem mem_locRing {y : X} {f : X.functionField} : f ∈ locRing y ↔ RegAt y f := Iff.rfl

def LogUnit (Z : Set X) (y : X) (g : X.functionFieldˣ) : Prop :=
  ∀ z : X, z ⤳ y → z ∉ Z → UnitAt z (g : X.functionField)

def logAt (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X) : AddSubgroup (abelian₂ X.functionField) :=
  spanForms {c | G.RegularAt y c} (dlog '' {g | LogUnit Z y g}) a

omit [IsIntegral X] in

def latSec {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V :=
  ⨅ y ∈ U, M y

abbrev logSec (Z : Set X) (G : CartierDiv X) (a : ℕ) (U : X.Opens) :
    AddSubgroup (abelian₂ X.functionField) :=
  latSec (logAt Z G a) U

structure IsLogChart (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop where

  chart : ∀ y ∈ U, AlgChart (locRing y) x

  logUnit : ∀ y ∈ U, ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
    ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y (u : X.functionField) ∧ g = u * ∏ j ∈ J, x j ^ m j

def IsSncOn {C : Type} (E : C → CartierDiv X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop :=
  ∃ e : C → Option (Fin n), (∀ c c' j, e c = some j → e c' = some j → c = c') ∧
    (∀ j, j ∈ J ↔ ∃ c, e c = some j) ∧
    ∀ c, ∀ y ∈ U, (E c).IsEqn y ((e c).elim 1 x)

def suppAll {C : Type} (E : C → CartierDiv X) : Set X := ⋃ c, ((E c).supp : Set X)

structure SncAtlas {C : Type} (E : C → CartierDiv X) (n : ℕ) (ι : Type) where

  U : ι → X.Opens

  x : ι → Fin n → X.functionFieldˣ

  J : ι → Finset (Fin n)

  affine : ∀ i, IsAffineOpen (U i)

  gen : ∀ i, genericPoint X ∈ U i

  cover : ⨆ i, U i = ⊤

  chart : ∀ i, IsLogChart (suppAll E) (U i) (x i) (J i)

  snc : ∀ i, IsSncOn E (U i) (x i) (J i)

structure LatModel {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V)
    (F : X.Modules) where

  val : ∀ U : X.Opens, genericPoint X ∈ U → (Γ(F, U) →+ V)

  inj : ∀ U h, Function.Injective (val U h)

  range : ∀ U h, (val U h).range = latSec M U

  res : ∀ (U W : X.Opens) (e : W ≤ U) (h : genericPoint X ∈ W) (s : Γ(F, U)),
    val W h (F.presheaf.map (homOfLE e).op s) = val U (e h) s

  smul : ∀ U h (r : Γ(X, U)) (s : Γ(F, U)), val U h (r • s) = fnOf U h r • val U h s

end Scheme

end GlobalTheory.LogDR
