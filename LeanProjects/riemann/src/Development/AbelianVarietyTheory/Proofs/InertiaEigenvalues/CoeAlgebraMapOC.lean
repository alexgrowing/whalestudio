import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem norm_zC (x : ℤ_[l]) : ‖zC x‖ = ‖x‖ := by
  unfold zC
  rw [norm_algebraMap']
  rfl

theorem mem_OC (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  simp only [Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding]
  rw [Valuation.embedding_restrict]
  exact NNReal.coe_le_one.symm

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (h : IsActC act) (g : GQ l)
    (x : ℤ_[l]) : act g (zC x) = zC x := by
  have h1 : zC x = ((algebraMap ℚ_[l] (Om l) (x : ℚ_[l]) : Om l) : PadicComplex l) := rfl
  rw [h1, h.1, AlgEquiv.commutes]

def zOC (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* OC l :=
  ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).codRestrict (PadicComplexInt l)
    (fun x => (mem_OC _).2 ((norm_zC x).le.trans x.norm_le_one))

scoped instance algOC : Algebra ℤ_[l] (OC l) := (zOC l).toAlgebra

theorem coe_algebraMap_OC (x : ℤ_[l]) :
    ((algebraMap ℤ_[l] (OC l) x : OC l) : PadicComplex l) = zC x := rfl

abbrev OCO (LL : FinExt l) : Type := OC l ⊗[ℤ_[l]] ↥(OL LL)

def gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) : RA LL →ₐ[↥(OL LL)] RA LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom g).toAlgHom

def IsThetaShift {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : Prop :=
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actWHom g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n)

def thR (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : RA LL →+* OCO LL :=
  ((Algebra.TensorProduct.comm ℤ_[l] ↥(OL LL) (OC l)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL)) θ)).toRingHom

theorem thR_tmul (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) (w : Ainf l) :
    thR LL θ (a ⊗ₜ[ℤ_[l]] w) = θ w ⊗ₜ[ℤ_[l]] a := rfl

def kap {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL) (k : Fin f) :
    PadicComplex l :=
  (((Algebra.TensorProduct.basis (OC l) o).repr x k : OC l) : PadicComplex l)

theorem kap_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (c : OC l)
    (a : ↥(OL LL)) (k : Fin f) :
    kap o (c ⊗ₜ[ℤ_[l]] a) k = (c : PadicComplex l) * zC (o.repr a k) := by
  simp [kap, Algebra.TensorProduct.basis_repr_tmul, coe_algebraMap_OC]

theorem kap_add {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x y : OCO LL)
    (k : Fin f) : kap o (x + y) k = kap o x k + kap o y k := by
  simp [kap]

theorem kap_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (k : Fin f) : kap o 0 k = 0 := by
  simp [kap]

theorem kap_tmul_one_mul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (c : OC l) (x : OCO LL) (k : Fin f) :
    kap o ((c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x) k = (c : PadicComplex l) * kap o x k := by
  have : (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x = c • x := by
    rw [Algebra.smul_def]; rfl
  rw [this]
  simp [kap]

theorem norm_kap_le {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL)
    (k : Fin f) : ‖kap o x k‖ ≤ 1 := (mem_OC _).1 (Subtype.property _)

def lam {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x : OCO LL) :
    Matrix (Fin d) (Fin d) (PadicComplex l) :=
  ∑ k, kap o x k • A (o k)

theorem freeOL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem finiteOL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem inclR_injective (LL : FinExt l) : Function.Injective (inclR LL) := by
  haveI := freeOL LL
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ↥(OL LL)) (inclWA l).toLinearMap
    (WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l)))

set_option synthInstance.maxHeartbeats 400000 in
theorem inclR_gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (r : RA LL) :
    inclR LL (gRA AI LL g r) = AI.gRW LL g (inclR LL r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w =>
    exact congrArg (fun u => a ⊗ₜ[ℤ_[l]] u) (inclW_act AI g w).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem kap_thR_gRA {P : LocPrime l} (AI : LocAinf l P) {LL : FinExt l} {f n : ℕ}
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {θ : Ainf l →ₐ[ℤ_[l]] OC l} (hθ : IsThetaShift AI n θ)
    (g : GQ l) (r : RA LL) (k : Fin f) :
    kap o (thR LL θ (gRA AI LL g r)) k = AI.actC g (kap o (thR LL θ r) k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero]
  | add x y hx hy => simp only [map_add, kap_add, hx, hy]
  | tmul a w =>
    have h1 : gRA AI LL g (a ⊗ₜ[ℤ_[l]] w) = a ⊗ₜ[ℤ_[l]] AI.actWHom g w := rfl
    rw [h1, thR_tmul, thR_tmul, kap_tmul, kap_tmul, map_mul, hθ.1, act_zC ⟨AI.actC_ext, AI.actC_norm⟩]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']

scoped instance (priority := high) twModule (T : LocLat G Qp LL O) : Module R (TW R T) :=
  inferInstance

scoped instance (priority := high) twSMul (T : LocLat G Qp LL O) : SMul R (TW R T) :=
  inferInstance

theorem TWincl_smul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem TWact_smul (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R) (z : TW R T) :
    TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']

theorem TWincl_act (f : R →ₐ[O] R') (u : R →ₐ[O] R) (u' : R' →ₐ[O] R') (h : ∀ r, f (u r) = u' (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWincl f T (TWact u T g z) = TWact u' T g (TWincl f T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a t => simp [TWact, TWincl, h]

theorem TWincl_injective (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G Qp LL O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem TWincl_one_tmul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWincl f T ((1 : R) ⊗ₜ[O] t) = (1 : R') ⊗ₜ[O] t := by
  simp [TWincl]

end Generic

end GlobalTheory.Cyc.Decomp
