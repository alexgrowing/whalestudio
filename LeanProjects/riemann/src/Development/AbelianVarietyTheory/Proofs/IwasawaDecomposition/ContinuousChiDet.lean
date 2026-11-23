import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (χ : HChar E)

def twR : GA E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) where
  toFun g := (((chiDet a χ g)⁻¹ : ℂˣ) : ℂ) • R (latticeGL E a) μ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

def Repr (F : L2 (latticeGL E a) μ) (φ : GA E a → ℂ) : Prop :=
  lift (latticeGL E a) F =ᵐ[μ] fun g => φ g * ((chiDet a χ g : ℂˣ) : ℂ)

def cls (V : Submodule ℂ (Sm E a)) : Submodule ℂ (L2 (latticeGL E a) μ) :=
  classes (V.map (mulChi a χ).toLinearMap) μ

variable {μ χ}

namespace Repr

variable {F F' : L2 (latticeGL E a) μ} {φ φ' : GA E a → ℂ}

theorem twR (h : Repr μ χ F φ) (k : GA E a) : Repr μ χ (twR μ χ k F) fun g => φ (g * k) := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_smul (((chiDet a χ k)⁻¹ : ℂˣ) : ℂ) (R (latticeGL E a) μ k F)),
    lift_R k F, (measurePreserving_mul_right μ k).quasiMeasurePreserving.ae h] with g e1 e2 e3
  refine e1.trans ?_
  change _ * lift _ (R (latticeGL E a) μ k F) g = _
  rw [e2, e3, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

omit [μ.IsMulRightInvariant]

theorem zero : Repr μ χ 0 0 := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 (AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ))] with g e
  exact e.trans (zero_mul _).symm

theorem add (h : Repr μ χ F φ) (h' : Repr μ χ F' φ') : Repr μ χ (F + F') (φ + φ') := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_add F F'), h, h'] with g e1 e2 e3
  exact e1.trans ((congrArg₂ (· + ·) e2 e3).trans (add_mul _ _ _).symm)

theorem smul (h : Repr μ χ F φ) (c : ℂ) : Repr μ χ (c • F) (c • φ) := by
  filter_upwards [ae_quotMeasure_iff.1 (Lp.coeFn_smul c F), h] with g e1 e2
  exact e1.trans ((congrArg (c * ·) e2).trans (mul_assoc _ _ _).symm)

theorem sum {ι : Type*} (s : Finset ι) {F : ι → L2 (latticeGL E a) μ} {φ : ι → GA E a → ℂ}
    (h : ∀ i ∈ s, Repr μ χ (F i) (φ i)) : Repr μ χ (∑ i ∈ s, F i) (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem unique (h : Repr μ χ F φ) (h' : Repr μ χ F' φ) : F = F' := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h.trans h'.symm)

end Repr

end GlobalTheory.OneRep

end
