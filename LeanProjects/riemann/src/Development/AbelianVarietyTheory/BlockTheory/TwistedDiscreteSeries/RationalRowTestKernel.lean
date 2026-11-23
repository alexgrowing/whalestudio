import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

section Abstract

variable {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E]

def HasRationalTest (σ : K →+* ℂ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ e ∈ S, ∀ a, ∃ z : K, σ z = ψ a e

example : HasRationalTest (algebraMap ℚ ℂ) ({Complex.I} : Set ℂ) := by
  refine ⟨1, fun _ => (-Complex.I) • LinearMap.id, fun e he => ?_, ?_⟩
  · simpa using he 0
  · rintro e rfl a
    exact ⟨1, by simp⟩

example : ¬ HasRationalTest (algebraMap ℚ ℂ) ({1, Complex.I} : Set ℂ) := by
  rintro ⟨n, ψ, hinj, hrat⟩
  refine one_ne_zero (hinj 1 fun a => ?_)
  obtain ⟨p, hp⟩ := hrat 1 (by simp) a
  obtain ⟨q, hq⟩ := hrat Complex.I (by simp) a
  have h : ψ a Complex.I = Complex.I * ψ a 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [← hp, ← hq] at h
  have h2 := congrArg Complex.im h
  simp at h2
  rw [← hp]
  have hp0 : p = 0 := by exact_mod_cast h2.symm
  simp [hp0]

end Abstract

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def RowTest (X : CxData A) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (X.EE →ₗ[ℂ] ℂ)), (∀ e : X.EE, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : Bs.Tup) (x : A.FR t) (a : Fin n), ∃ z : K, Bs.v0.embedding z = ψ a (X.Θ t (X.jR t x))

def rationalRows (X : CxData A) : Set X.EE := {e | ∃ (t : Bs.Tup) (x : A.FR t), X.Θ t (X.jR t x) = e}

def FormsSpan (X : CxData A) : Prop := ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def KerRational (X : CxData A) : Prop :=
  ∀ t, Submodule.span ℂ (X.jR t '' {x : A.FR t | X.Θ t (X.jR t x) = 0}) = LinearMap.ker (X.Θ t)

def KerRationalOfRowTest : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (X : CxData A),
    FormsSpan X → RowTest X → KerRational X

def RatMuOfRowTest : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (b : Bool), X.H2 cr b → RowTest X → X.RATmu cr b

end Interface

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowTestAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → RowTest (R.toCx F)

def RowTestModel (R : RealDat D A Ks) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (R.HE.H →ₗ[ℂ] ℂ)), (∀ e : R.HE.H, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), ∃ z : D.what₂.LL, D.what₂.embLL z = ψ a (R.Th t (R.jX t x))

def twFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E →ₗ[ℂ] ℂ) : Tw s E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.out x))
  map_add' x y := by rw [Tw.out_add, map_add, map_add]
  map_smul' z x := by rw [Tw.out_smul, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

def untwFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Tw s E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.mkL s E x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' z x := by rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

theorem test_tw_iff {K E : Type} [Field K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {σ σ' : K →+* ℂ}
    (h : ∀ a, σ' a = cj s (σ a)) {ι : Type} {X : ι → Type} (v : ∀ t, X t → E) :
    (∃ (n : ℕ) (ψ : Fin n → (Tw s E →ₗ[ℂ] ℂ)), (∀ e : Tw s E, (∀ a, ψ a e = 0) → e = 0) ∧
      ∀ t x a, ∃ z : K, σ' z = ψ a (Tw.mk s (v t x))) ↔
    (∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ t x a, ∃ z : K, σ z = ψ a (v t x)) := by
  constructor
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => untwFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    refine ⟨z, ?_⟩
    have := congrArg (cj s) ((h z).symm.trans hz)
    rw [cj_cj] at this
    exact this
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => twFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    exact ⟨z, (h z).trans (congrArg (cj s) hz)⟩

theorem rowTest_toCx_iff (R : RealDat D A Ks) (F : Face D A) : RowTest (R.toCx F) ↔ RowTestModel R :=
  test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A.v0) R.emb0 (ι := T) (X := fun t => A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)

def RowTestAlgAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∃ (n : ℕ) (ψ : Fin n → ((R.toCx F).EE →ₗ[ℂ] ℂ)), (∀ e, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), IsAlgebraic ℚ (ψ a ((R.toCx F).Θ t ((R.toCx F).jR t x)))

def KerRationalAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → KerRational (R.toCx F)

def RatMuAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∀ b, (R.toCx F).RATmu F.cr b

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

end
