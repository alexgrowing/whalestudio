import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RationalTransitionKernel

open NumberField
open scoped Matrix InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.EquivariantEuclideanComplex

open Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel

section Lin

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)

theorem cpt_single {n : ℕ} (k : Fin n) : cpt v.embedding (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases hi : i = k <;> simp [cpt, hi]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

theorem ext_cpt {n : ℕ} {f g : (Fin n → ℂ) →ₗ[ℂ] E}
    (h : ∀ x : Fin n → K, f (cpt v.embedding x) = g (cpt v.embedding x)) : f = g := by
  rw [← lin_basis f, ← lin_basis g]
  congr 1
  funext i
  rw [← cpt_single v i, h]

def RatRel {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (g : (Fin n → ℂ) →ₗ[ℂ] E) : Prop :=
  ∃ Y : Matrix (Fin D) (Fin n) K, Function.Bijective Y.mulVec ∧ g = f ∘ₗ cx v Y

end Lin

section Dict

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J}

def thetaOf (X : CxData F.amb) (t : T) : (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] X.EE :=
  lin fun k => X.Θ t (X.jR t ((F.R t).S.basis k))

def IsCoord {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) (Zs : DefSub F.amb)
    (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ t, Function.Injective (cr.toR Zs b t) ∧
    LinearMap.range (cr.toR Zs b t) = LinearMap.range ((F.R t).toF (F.lvl P ψ) (Zs.Z t))

def RowsBij (X : CxData F.amb) {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) : Prop :=
  ∀ t, Function.Injective (X.iC cr b t) ∧ LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b F.μ0)

def MetricTie (X : CxData F.amb) : Prop :=
  ∀ t, ∃ c : ℝ, 0 < c ∧ ∀ x y : Fin (F.R t).S.dim → K,
    ⟪X.jR t ((F.R t).S.basis.equivFun.symm x), X.jR t ((F.R t).S.basis.equivFun.symm y)⟫_ℂ =
      (c : ℂ) * F.v0.embedding (hform (F.R t).S.H x y)

variable (X : CxData F.amb) {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool)
  (P : Subgroup G) (ψ : P →* Kˣ)

theorem orth_span {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {S : Set A} {f : A}
    (hf : ∀ p ∈ S, ⟪p, f⟫_ℂ = 0) : ∀ p ∈ Submodule.span ℂ S, ⟪p, f⟫_ℂ = 0 := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hf x hx
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

def EquivariantRat (ρ : Representation ℂ G X.EE) : Prop :=
  ∀ (t : T) (g : G), ∀ x ∈ (F.R t).goodF F.X, X.Θ t (X.jR t ((F.R t).r g x)) = ρ g (X.Θ t (X.jR t x))

end Dict

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem isCoord_base (Zs : DefSub A.fam.amb) : IsCoord (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false Zs P0 ψ0 :=
  fun t => ⟨(A.fam.R t).toF_injective _ _, rfl⟩

end Concrete

section Onto

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE)

def fr (t : T) : Matrix (Fin (F.R t).S.dim) (Fin (F.R t).S.dim) ℂ := frameOf ((F.R t).S.H.map F.v0.embedding)

def toEuc (t : T) : (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (F.R t).S.dim) :=
  (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).symm.toLinearMap ∘ₗ (fr F t)⁻¹.mulVecLin

def ofEuc (t : T) : EuclideanSpace ℂ (Fin (F.R t).S.dim) →ₗ[ℂ] (Fin (F.R t).S.dim → ℂ) :=
  (fr F t).mulVecLin ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin (F.R t).S.dim → ℂ)).toLinearMap

def cxOf : CxData F.amb where
  FC t := EuclideanSpace ℂ (Fin (F.R t).S.dim)
  jR t := (toEuc F t).comp ((cptL F.v0.embedding _).comp
    ((F.R t).S.basis.equivFun : (F.R t).S.Forms →ₗ[K] (Fin (F.R t).S.dim → K)))
  EE := EE
  Θ t := Θ t ∘ₗ ofEuc F t
  EEp _ := ⊤
  EEl _ := ⊤
  FLC _ _ := EuclideanSpace ℂ (Fin 0)
  jL _ _ := 0
  W _ := EuclideanSpace ℂ (Fin 0)
  θ' _ _ := 0
  Wp _ _ := ⊤
  dW _ _ := 0
  WC _ _ _ := EuclideanSpace ℂ (Fin 0)
  bW _ _ _ _ := 0
  eW _ _ := 0
  M _ _ := ⊤
  nP _ := 1
  μ _ := F.μ0
  Tw := ∅
  κ _ := 1
  lam _ _ _ _ := 1
  err0 _ _ := 0

variable {F} {s : ℕ} (hF : F.Ok s)

include hF

end Onto

example {K : Type} [Field K] (σ : K →+* ℂ) :
    IsRat σ (relMat (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) LinearMap.id) := by
  intro i k
  refine ⟨0, ?_⟩
  have h : ¬ ∃ y, (0 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) y = Pi.single k 1 := by
    rintro ⟨y, hy⟩
    simpa using congrFun hy k
  simp only [relMat, Matrix.of_apply, LinearMap.id_apply, solve, dif_neg h, map_zero, Pi.zero_apply]

end GlobalTheory.EquivariantEuclideanComplex
