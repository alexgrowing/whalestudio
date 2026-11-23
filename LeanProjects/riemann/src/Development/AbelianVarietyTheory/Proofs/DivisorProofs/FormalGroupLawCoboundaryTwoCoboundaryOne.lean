import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

namespace CobCob

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.elim_has {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [hu, hv])

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.op_const
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ u v i) = 0 := by
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.at2
  exact constantCoeff_subst_eq_zero (_root_.GlobalTheory.Katz.CobCob.elim_has hu hv)
    (by rintro (j | j) <;> simp [hu, hv]) (h i)

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x1
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x2
  exact constantCoeff_X _

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
theorem _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) i) = 0 := by
  unfold _root_.GlobalTheory.Katz.x3
  exact constantCoeff_X _

theorem powerSeriesEvalTwoGroups_sub {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 (c - c') u v = at2 c u v - at2 c' u v := subst_sub (elim_has hu hv) _ _

theorem powerSeriesEvalTwoGroups_smul {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 (r • c) u v = r • at2 c u v := subst_smul (elim_has hu hv) _ _

end CobCob

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_sub_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c - c') u v =
      _root_.GlobalTheory.Katz.at2 c u v - _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_sub h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_subst_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (subst a f) u v =
      subst (fun i => _root_.GlobalTheory.Katz.at2 (a i) u v) f := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) h f

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_X_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (s : Fin d ⊕ Fin d) :
    _root_.GlobalTheory.Katz.at2 (X s) u v = Sum.elim u v s := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_X h s

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_cob1_eq_subst_op_sub {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (_root_.GlobalTheory.Katz.cob1 μ f) u v =
      subst (_root_.GlobalTheory.Katz.op μ u v) f - subst u f - subst v f := by
  unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
  rw [at2_sub_of_hasSubst h, at2_sub_of_hasSubst h,
    at2_subst_of_hasSubst h hμ,
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _),
    at2_subst_of_hasSubst h (fun i => constantCoeff_X _)]
  simp only [at2_X_of_hasSubst h, Sum.elim_inl, Sum.elim_inr]
  rfl

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (c + c') u v =
      _root_.GlobalTheory.Katz.at2 c u v + _root_.GlobalTheory.Katz.at2 c' u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_add h c c'

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem at2_smul_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    _root_.GlobalTheory.Katz.at2 (r • c) u v = r • _root_.GlobalTheory.Katz.at2 c u v := by
  unfold _root_.GlobalTheory.Katz.at2
  exact subst_smul h r c

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in
variable {R : Type} [CommRing R] {d : ℕ} {τ : Type} in
private theorem op_addLaw_eq_add_of_hasSubst {u v : Fin d → MvPowerSeries τ R}
    (h : HasSubst (Sum.elim u v)) :
    _root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) u v = fun i => u i + v i := by
  funext i
  unfold _root_.GlobalTheory.Katz.op _root_.GlobalTheory.Katz.addLaw
  rw [at2_add_of_hasSubst h, at2_X_of_hasSubst h,
    at2_X_of_hasSubst h]
  rfl

set_option autoImplicit false in
open CategoryTheory TensorProduct MvPowerSeries in

theorem _root_.GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt : ∀ (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ f : MvPowerSeries (Fin d) R,
    _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f ∧
    _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f ∧
    (∀ c c', _root_.GlobalTheory.Katz.cob2 μ (c + c') =
      _root_.GlobalTheory.Katz.cob2 μ c + _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.cob2 μ (c - c') =
      _root_.GlobalTheory.Katz.cob2 μ c - _root_.GlobalTheory.Katz.cob2 μ c' ∧
      _root_.GlobalTheory.Katz.swap (c - c') =
      _root_.GlobalTheory.Katz.swap c - _root_.GlobalTheory.Katz.swap c') ∧
    (∀ (r : R) c, _root_.GlobalTheory.Katz.cob2 μ (r • c) = r • _root_.GlobalTheory.Katz.cob2 μ c ∧
      _root_.GlobalTheory.Katz.swap (r • c) = r • _root_.GlobalTheory.Katz.swap c) ∧
    _root_.GlobalTheory.Katz.IsLaw (_root_.GlobalTheory.Katz.addLaw R d) ∧
    (_root_.GlobalTheory.Katz.IsLaw μ →
      _root_.GlobalTheory.Katz.IsCoc μ (_root_.GlobalTheory.Katz.cob1 μ f)) := by
  intro R _ d μ hμ f
  have h1 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)
  have h2 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)
  have h3 := _root_.GlobalTheory.Katz.CobCob.constantCoeff_threeGroupsThirdVariables (R := R) (d := d)
  have h23 := _root_.GlobalTheory.Katz.CobCob.elim_has h2 h3
  have h12 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 h2
  have h12_3 := _root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hμ h1 h2) h3
  have h1_23 := _root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hμ h2 h3)
  have hs : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    _root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X _) (fun i => constantCoeff_X _)
  have part1 : _root_.GlobalTheory.Katz.cob2 μ (_root_.GlobalTheory.Katz.cob1 μ f) =
      subst (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) f -
      subst (_root_.GlobalTheory.Katz.op μ
        (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
        _root_.GlobalTheory.Katz.x3) f := by
    unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_cob1_eq_subst_op_sub h23 hμ, at2_cob1_eq_subst_op_sub h12_3 hμ,
      at2_cob1_eq_subst_op_sub h1_23 hμ, at2_cob1_eq_subst_op_sub h12 hμ]
    abel
  have part2 : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) -
      _root_.GlobalTheory.Katz.cob1 μ f =
      subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f - subst μ f := by
    have e : _root_.GlobalTheory.Katz.swap (_root_.GlobalTheory.Katz.cob1 μ f) =
        subst (fun i => _root_.GlobalTheory.Katz.swap (μ i)) f -
          _root_.GlobalTheory.Katz.inR f - _root_.GlobalTheory.Katz.inL f :=
      at2_cob1_eq_subst_op_sub hs hμ f
    rw [e]
    unfold _root_.GlobalTheory.Katz.cob1
    abel
  refine ⟨part1, part2, fun c c' => ⟨?_, ?_, ?_⟩, fun r c => ⟨?_, ?_⟩, ?_, fun hl => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_add_of_hasSubst h23, at2_add_of_hasSubst h12_3,
      at2_add_of_hasSubst h1_23, at2_add_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_sub_of_hasSubst h23, at2_sub_of_hasSubst h12_3,
      at2_sub_of_hasSubst h1_23, at2_sub_of_hasSubst h12]
    abel
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_sub_of_hasSubst hs c c'
  · unfold _root_.GlobalTheory.Katz.cob2
    rw [at2_smul_of_hasSubst h23, at2_smul_of_hasSubst h12_3,
      at2_smul_of_hasSubst h1_23, at2_smul_of_hasSubst h12]
    simp only [smul_sub, smul_add]
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_smul_of_hasSubst hs r c
  · have hc : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
      intro i
      simp [_root_.GlobalTheory.Katz.addLaw]
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [op_addLaw_eq_add_of_hasSubst
        (_root_.GlobalTheory.Katz.CobCob.elim_has (fun i => constantCoeff_X i) (fun _ => by simp))]
      funext i
      simp
    · intro i
      unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.addLaw
      rw [at2_add_of_hasSubst hs, at2_X_of_hasSubst hs,
        at2_X_of_hasSubst hs]
      simp [add_comm]
    · rw [op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has (_root_.GlobalTheory.Katz.CobCob.op_const hc h1 h2) h3),
        op_addLaw_eq_add_of_hasSubst h12,
        op_addLaw_eq_add_of_hasSubst
          (_root_.GlobalTheory.Katz.CobCob.elim_has h1 (_root_.GlobalTheory.Katz.CobCob.op_const hc h2 h3)),
        op_addLaw_eq_add_of_hasSubst h23]
      funext i
      exact add_assoc _ _ _
  · unfold _root_.GlobalTheory.Katz.IsCoc
    constructor
    · rw [part1, hl.assoc, sub_self]
    · rw [← sub_eq_zero, part2]
      simp [hl.comm]

end Katz

end GlobalTheory
