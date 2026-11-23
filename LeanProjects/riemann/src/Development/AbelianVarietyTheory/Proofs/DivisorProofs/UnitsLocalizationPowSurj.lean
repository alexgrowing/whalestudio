import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPowEq
open IsLocalRing

namespace GlobalTheory.LocAcycUnits

open Polynomial

theorem units_pow_surj_of_sepClosed (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hq0 : 0 < q) (w : Oˣ) :
    ∃ v : Oˣ, v ^ q = w := by
  first
  | exact @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | (apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq ..)

theorem units_localization_pow_surj : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ v : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, v ^ q = u := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hO u
  obtain ⟨_, hroot⟩ := hT
  obtain ⟨c, d, w, hc, hd, hu⟩ := GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit T O hroot hO u
  set L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have root : ∀ x : T, x ≠ 0 → ∃ y : T, y ≠ 0 ∧ y ^ q = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hroot (X ^ q - C x) (monic_X_pow_sub_C _ hq0.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hq0)
    have hyq : y ^ q = x := by simpa [sub_eq_zero] using hy
    refine ⟨y, ?_, hyq⟩
    rintro rfl; exact hx (by rw [← hyq, zero_pow hq0.ne'])
  have unitOf : ∀ x : T, x ≠ 0 → IsUnit (algebraMap O L (algebraMap T O x)) := fun x hx =>
    IsLocalization.map_units L (⟨algebraMap T O x,
      Algebra.mem_algebraMapSubmonoid_of_mem (⟨x, mem_nonZeroDivisors_of_ne_zero hx⟩ :
        nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  obtain ⟨c', hc', hcq⟩ := root c hc
  obtain ⟨d', hd', hdq⟩ := root d hd
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  obtain ⟨w', hw'⟩ := units_pow_surj_of_sepClosed O q hqO hq0 w
  have powU : ∀ (x y : T) (hx : x ≠ 0) (hy : y ≠ 0), y ^ q = x →
      (unitOf y hy).unit ^ q = (unitOf x hx).unit := by
    intro x y hx hy hxy
    apply Units.ext
    simp [← map_pow, hxy]
  have hMw : (Units.map (algebraMap O L).toMonoidHom w') ^ q = Units.map (algebraMap O L).toMonoidHom w := by
    rw [← map_pow, hw']
  have huU : u * (unitOf d hd).unit = (unitOf c hc).unit * Units.map (algebraMap O L).toMonoidHom w := by
    apply Units.ext; simpa using hu
  refine ⟨(unitOf c' hc').unit * Units.map (algebraMap O L).toMonoidHom w' * (unitOf d' hd').unit⁻¹, ?_⟩
  rw [mul_pow, mul_pow, inv_pow, powU c c' hc hc' hcq, powU d d' hd hd' hdq, hMw, ← huU]
  group

end GlobalTheory.LocAcycUnits
