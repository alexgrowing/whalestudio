import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMem

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

section Zl

@[reducible] def zlT (T : QLat LL) : Module ℤ_[l] ↥T.L.T := Module.compHom _ (algebraMap ℤ_[l] ↥(OL LL))

@[reducible] def zlV (T : QLat LL) : Module ℤ_[l] T.V := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

@[reducible] def zlB (Pl : LocPrime l) : Module ℤ_[l] Pl.R.B := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

attribute [local instance] zlT zlV zlB

theorem towT (T : QLat LL) : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towV (T : QLat LL) : IsScalarTower ℤ_[l] ℚ_[l] T.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towB (Pl : LocPrime l) : IsScalarTower ℤ_[l] ℚ_[l] Pl.R.B :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] towT towV towB

def incl (T : QLat LL) : ↥T.L.T →ₗ[ℤ_[l]] T.V where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' z x := by
    change ((algebraMap ℤ_[l] ↥(OL LL) z • x : ↥T.L.T) : T.V) = algebraMap ℤ_[l] ℚ_[l] z • (x : T.V)
    rw [Submodule.coe_smul, ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) (x : T.V),
      ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) (x : T.V)]
    rfl

theorem exists_pow_mul_mem (LL : FinExt l) (a : ↥LL.1) :
    ∃ k : ℕ, (l : ↥LL.1) ^ k * a ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
    (PadicInt.irreducible_p (p := l))
  refine ⟨k, ?_⟩
  have h3 := hi.smul ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast] at h3
  exact h3

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem zl_smul_V (T : QLat LL) (z : ℤ_[l]) (v : T.V) : z • v = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) • v := by
  change algebraMap ℤ_[l] ℚ_[l] z • v = _
  rw [← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) v]
  rfl

theorem isLoc (T : QLat LL) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (incl T) := by
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, ?_⟩⟩
  · have hs : ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rw [Ne, PadicInt.coe_eq_zero]; exact nonZeroDivisors.coe_ne_zero s
    have hs' : algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    refine (Module.End.isUnit_iff _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, zl_smul_V, zl_smul_V] at hab
      exact smul_right_injective _ hs' hab
    · refine ⟨(algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]))⁻¹ • a, ?_⟩
      rw [Module.algebraMap_end_apply, zl_smul_V, smul_smul, mul_inv_cancel₀ hs', one_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_mem T y
    have hl : ((l : ℤ_[l]) ^ n) ∈ nonZeroDivisors ℤ_[l] :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    refine ⟨(⟨_, hn⟩, ⟨_, hl⟩), ?_⟩
    show ((l : ℤ_[l]) ^ n) • y = (l : ↥LL.1) ^ n • y
    rw [zl_smul_V]
    congr 1
    simp
  · simp only [one_smul]; exact Subtype.ext h

theorem hbc (T : QLat LL) : IsBaseChange ℚ_[l] (incl T) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] (incl T)).1 (isLoc T)

variable {Bc : Type} [CommRing Bc] [Algebra ℤ_[l] Bc] {Pl : LocPrime l}

def ringLin (eB : Pl.R.B ≃+* Bc) (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    Bc ≃ₗ[ℤ_[l]] Pl.R.B :=
  { eB.symm.toAddEquiv with
    map_smul' := fun z b => by
      show eB.symm (z • b) = algebraMap ℤ_[l] ℚ_[l] z • eB.symm b
      rw [Algebra.smul_def z b, map_mul, Algebra.smul_def]
      congr 1
      rw [RingEquiv.symm_apply_eq]
      exact (hz z).symm }

def swapLat (T : QLat LL) : TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) :=
  TensorProduct.comm ↥(OL LL) (↥(OL LL) ⊗[ℤ_[l]] Bc) ↥T.L.T

def cancelCoeff (T : QLat LL) : ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[ℤ_[l]] Bc :=
  AlgebraTensorModule.cancelBaseChange ℤ_[l] ↥(OL LL) ↥(OL LL) ↥T.L.T Bc

def changeRing (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    ↥T.L.T ⊗[ℤ_[l]] Bc ≃ₗ[ℤ_[l]] Pl.R.B ⊗[ℤ_[l]] ↥T.L.T :=
  (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ↥T.L.T) (ringLin eB hz)).trans (TensorProduct.comm ℤ_[l] ↥T.L.T Pl.R.B)

variable (Pl) in

def invertPrime (T : QLat LL) : Pl.R.B ⊗[ℤ_[l]] ↥T.L.T ≃ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (AlgebraTensorModule.cancelBaseChange ℤ_[l] ℚ_[l] ℚ_[l] Pl.R.B ↥T.L.T).symm.trans
     ((TensorProduct.congr (LinearEquiv.refl ℚ_[l] Pl.R.B) (hbc T).equiv).trans
       (TensorProduct.comm ℚ_[l] Pl.R.B T.V))

def addEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃+ T.V ⊗[ℚ_[l]] Pl.R.B :=
  (((swapLat T).trans (cancelCoeff T)).toAddEquiv.trans (changeRing T eB hz).toAddEquiv).trans (invertPrime Pl T).toAddEquiv

theorem addEquiv_tmul (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z)
    (o : ↥(OL LL)) (b : Bc) (x : ↥T.L.T) :
    addEquiv T eB hz ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = (((o • x : ↥T.L.T)) : T.V) ⊗ₜ[ℚ_[l]] eB.symm b := by
  simp [addEquiv, swapLat, cancelCoeff, changeRing, invertPrime, ringLin, IsBaseChange.equiv_tmul, incl]

end Zl

variable {Pl : LocPrime l}

theorem addEquiv_smul (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (c : ↥(OL LL)) (w : TW (OB l ↥(OL LL)) T) :
    addEquiv T eB hz (c • w) = c • addEquiv T eB hz w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy =>
    rw [smul_add, map_add, map_add]
    exact (congrArg₂ (· + ·) hx hy).trans (smul_add c _ _).symm
  | tmul y x =>
    rw [TensorProduct.smul_tmul']
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [smul_add, add_tmul, add_tmul, map_add, map_add]
      exact (congrArg₂ (· + ·) h₁ h₂).trans (smul_add c _ _).symm
    | tmul o b =>
      have e : (((c • o) • x : ↥T.L.T) : T.V) = (c : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
        rw [smul_assoc, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 c]
        rfl
      rw [TensorProduct.smul_tmul', addEquiv_tmul, addEquiv_tmul, e]
      exact (TensorProduct.smul_tmul' (c : ↥LL.1) _ _).symm

def linEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z) :
    TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (addEquiv T eB hz).toLinearEquiv (addEquiv_smul T eB hz)

theorem linEquiv_apply (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (w : TW (OB l ↥(OL LL)) T) : linEquiv T eB hz w = addEquiv T eB hz w := rfl

theorem linEquiv_one (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (x : ↥T.L.T) :
    linEquiv T eB hz ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B) := by
  rw [linEquiv_apply, Algebra.TensorProduct.one_def, addEquiv_tmul, one_smul, map_one]

theorem linEquiv_act (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hact : ∀ (g : GQ l) (b : Pl.R.B), eB (Pl.actQ g b) = Per.σB g (eB b))
    (g : Gl l) (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (actB (sQ l) T g w) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add, map_add, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (g : GQ l) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [actVB, AlgebraTensorModule.map_tmul]
      congr 1
      · rw [Submodule.coe_smul, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 o, ← algebraMap_smul ↥LL.1 o,
          map_smul]
        rfl
      · rw [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, Pl.PD_actB,
          RingEquiv.symm_apply_eq, hact, RingEquiv.apply_symm_apply]

theorem linEquiv_frob (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hfr : ∀ b : Pl.R.B, eB (Pl.φB b) = Per.φB l (eB b))
    (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (TWmap (frobOB l ↥(OL LL)) T w) =
      φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add, map_add, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : TWmap (frobOB l ↥(OL LL)) T ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.φB l b) ⊗ₜ[↥(OL LL)] x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [φVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      congr 1
      rw [AlgHom.toLinearMap_apply, Pl.PD_φ, RingEquiv.symm_apply_eq, hfr, RingEquiv.apply_symm_apply]

end GlobalTheory.BKGal.CrisTensor
