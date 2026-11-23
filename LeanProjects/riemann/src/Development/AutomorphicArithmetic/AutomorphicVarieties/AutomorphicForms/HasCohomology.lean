import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def regFun : Subalgebra ℂ (GL (Fin a) (Rinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ v i j, f = fun y => ((y.val i j v : ℝ) : ℂ)} ∪ {f | ∃ v, f = fun y => ((y.val.det v : ℝ) : ℂ)⁻¹})

variable (E a) in

structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Rinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

open Classical in

def extGL (f : GL (Fin a) (Rinf E) → ℂ) (x : Lie E a) : ℂ := if h : IsUnit (Matrix.of x) then f h.unit else 0

def AlgRep.dmat (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a) X
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp

open Classical in

def AlgRep.HasInfChar (Ξ : AlgRep E a) (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => Ξ.dmat (toL (Matrix.single i j (Pi.single v 1)))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

variable (E a) in

def AlgRep.triv : AlgRep E a where
  d := 1
  mat := 1
  reg i j := Subalgebra.algebraMap_mem _ ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
  pos := one_pos
  irred W _ := by
    have : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
    exact eq_bot_or_eq_top W

variable (E a) in

abbrev Herm : Submodule ℝ (Matrix (Fin a) (Fin a) (Rinf E)) := selfAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) (Rinf E))

def adHerm (k : Kinf E a) (X : Herm E a) : Herm E a := ⟨k.1 * X.1 * star k.1, IsSelfAdjoint.conjugate X.2 k.1⟩

section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

def IsCochain {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (k : Kinf E a), k.1.det = 1 → ∀ X : Fin q → Herm E a, ω (fun i => adHerm k (X i)) = κ k (ω X)

def dCo {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L (toL X.1)).restrictScalars ℝ).compAlternatingMap ω
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L (toL X.1) (toL Y.1)) (ω v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c (toL X.1)) (ω v) }

def HasCohomology : Prop :=
  (∃ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, IsCochain κ ω ∧ dCo L ω = 0 ∧ ω ≠ 0) ∨
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), IsCochain κ ω ∧ dCo L ω = 0 ∧
      ∀ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, IsCochain κ η → dCo L η ≠ ω

end Complex

variable [IsTotallyReal E]

def lieOp (π : CuspSub E a) : Lie E a →ₗ[ℝ] Module.End ℂ π.V where
  toFun X := π.op (.lie X)
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_add (lie E a) X Y) φ.1)
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_smul (lie E a) c X) φ.1)

def tensorK (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (π.op (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X), ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

def IsCohFor (π : CuspSub E a) (Ξ : AlgRep E a) : Prop := HasCohomology (tensorK π Ξ) (tensorLie π Ξ)

variable (E a) in

def GLplus : Subgroup (GL (Fin a) E) where
  carrier := {γ | ∀ τ : E →+* ℝ, 0 < τ γ.val.det}
  one_mem' τ := by simp
  mul_mem' {x y} hx hy τ := by simpa [Matrix.det_mul] using mul_pos (hx τ) (hy τ)
  inv_mem' {x} hx τ := by
    have h : τ (x⁻¹).val.det * τ x.val.det = 1 := by rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul]; simp
    have h2 := hx τ
    by_contra h3
    nlinarith [not_lt.1 h3]

def AlgRep.rat (Ξ : AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

omit [IsTotallyComplex E] in

def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)

omit [IsTotallyComplex E] in

def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
