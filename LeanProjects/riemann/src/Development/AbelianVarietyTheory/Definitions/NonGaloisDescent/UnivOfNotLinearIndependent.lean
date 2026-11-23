import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Matrix Formalism.IndefR.Datum

namespace GlobalTheory.ExportSeries

section Flat

variable {k R : Type} [CommRing k] [CommRing R] {r n : ℕ}

open Classical in

def flat (ν : kˣ →* Rˣ) (y : Matrix (Fin r) (Fin n) k) : R :=
  if h : IsUnit (topL r y).det then ((ν h.unit : Rˣ) : R) else 0

theorem flat_of_isUnit (ν : kˣ →* Rˣ) {y : Matrix (Fin r) (Fin n) k} {u : kˣ} (h : (topL r y).det = u) :
    flat ν y = ((ν u : Rˣ) : R) := by
  have hu : IsUnit (topL r y).det := h ▸ u.isUnit
  have hu' : hu.unit = u := Units.ext (by rw [IsUnit.unit_spec, h])
  unfold flat
  rw [dif_pos hu, hu']

theorem flat_of_not_isUnit (ν : kˣ →* Rˣ) {y : Matrix (Fin r) (Fin n) k} (h : ¬ IsUnit (topL r y).det) :
    flat ν y = 0 := by
  unfold flat
  rw [dif_neg h]

theorem topL_mul (hr : r ≤ n) (g : Matrix (Fin r) (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    topL r (g * y) = g * topL r y := by
  ext i j
  have hj : j.val < n := lt_of_lt_of_le j.isLt hr
  simp [topL, Matrix.mul_apply, hj]

theorem flat_mul (hr : r ≤ n) (ν : kˣ →* Rˣ) (g : GL (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    flat ν ((g : Matrix (Fin r) (Fin r) k) * y) = ((ν (GeneralLinearGroup.det g) : Rˣ) : R) * flat ν y := by
  have hdet : (topL r ((g : Matrix (Fin r) (Fin r) k) * y)).det =
      (GeneralLinearGroup.det g : k) * (topL r y).det := by
    rw [topL_mul hr, Matrix.det_mul]
    rfl
  by_cases hu : IsUnit (topL r y).det
  · rw [flat_of_isUnit ν (u := GeneralLinearGroup.det g * hu.unit) (by rw [hdet, Units.val_mul, hu.unit_spec]),
      flat_of_isUnit ν (u := hu.unit) hu.unit_spec.symm, map_mul, Units.val_mul]
  · have hu' : ¬ IsUnit (topL r ((g : Matrix (Fin r) (Fin r) k) * y)).det := by
      rw [hdet, Units.isUnit_units_mul]
      exact hu
    rw [flat_of_not_isUnit ν hu', flat_of_not_isUnit ν hu, mul_zero]

end Flat

section Univ

variable {k : Type} [Field k] {r n : ℕ}

open Classical in

def prim (y : Matrix (Fin r) (Fin n) k) : ℚ := if LinearIndependent k y.row then 1 else 0

def Compl (U : Submodule k (Fin n → k)) (y : Matrix (Fin r) (Fin n) k) : Prop :=
  Submodule.span k (Set.range y.row) ⊔ U = ⊤

variable (k r n) in

abbrev Planes : Type := {U : Submodule k (Fin n → k) // Module.finrank k U + r = n}

instance [Finite k] : Finite (Planes k r n) :=
  haveI : Finite (Submodule k (Fin n → k)) := Finite.of_injective _ SetLike.coe_injective
  Subtype.finite

theorem finrank_quot (U : Planes k r n) : Module.finrank k ((Fin n → k) ⧸ U.1) = r := by
  have h1 := Submodule.finrank_quotient_add_finrank U.1
  have h2 := U.2
  rw [Module.finrank_fin_fun] at h1
  omega

variable (k r n) in

structure DetBases where

  form : ∀ U : Planes k r n, ((Fin n → k) ⧸ U.1) [⋀^Fin r]→ₗ[k] k
  ne : ∀ U, form U ≠ 0

def DetBases.std (k : Type) [Field k] (r n : ℕ) : DetBases k r n where
  form U := (Module.finBasisOfFinrankEq k _ (finrank_quot U)).det
  ne _ := Module.Basis.det_ne_zero _

instance : Inhabited (DetBases k r n) := ⟨DetBases.std k r n⟩

def dU (β : DetBases k r n) (U : Planes k r n) (y : Matrix (Fin r) (Fin n) k) : k :=
  β.form U fun i => U.1.mkQ (y.row i)

theorem dU_ne_zero_iff (β : DetBases k r n) (U : Planes k r n) (y : Matrix (Fin r) (Fin n) k) :
    dU β U y ≠ 0 ↔ Compl U.1 y := by
  have hspan : Submodule.span k (Set.range fun i => U.1.mkQ (y.row i)) = ⊤ ↔ Compl U.1 y := by
    have hr : (Set.range fun i => U.1.mkQ (y.row i)) = U.1.mkQ '' Set.range y.row := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, Submodule.map_mkQ_eq_top, Compl, sup_comm]
  have hcard : Fintype.card (Fin r) = Module.finrank k ((Fin n → k) ⧸ U.1) := by
    rw [Fintype.card_fin, finrank_quot U]
  unfold dU
  rw [← hspan]
  constructor
  · intro hne
    have hli : LinearIndependent k (fun i => U.1.mkQ (y.row i)) := by
      by_contra hdep
      exact hne ((β.form U).map_linearDependent _ hdep)
    exact hli.span_eq_top_of_card_eq_finrank' hcard
  · intro htop
    have hli : LinearIndependent k (fun i => U.1.mkQ (y.row i)) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge hcard
    have hb := (β.form U).map_basis_ne_zero_iff (Module.Basis.mk hli htop.ge)
    rw [Module.Basis.coe_mk] at hb
    exact hb.2 (β.ne U)

theorem dU_mul (β : DetBases k r n) (U : Planes k r n) (g : Matrix (Fin r) (Fin r) k) (y : Matrix (Fin r) (Fin n) k) :
    dU β U (g * y) = g.det * dU β U y := by
  let e := Module.finBasisOfFinrankEq k ((Fin n → k) ⧸ U.1) (finrank_quot U)
  have hrow : ∀ i, U.1.mkQ ((g * y).row i) = ∑ j, g i j • U.1.mkQ (y.row j) := by
    intro i
    have hgy : (g * y).row i = ∑ j, g i j • y.row j := by
      ext c
      simp [Matrix.mul_apply, Matrix.row, Finset.sum_apply]
    rw [hgy, map_sum]
    simp only [map_smul]
  have hM : e.toMatrix (fun i => U.1.mkQ ((g * y).row i)) =
      e.toMatrix (fun i => U.1.mkQ (y.row i)) * g.transpose := by
    ext a i
    simp only [Module.Basis.toMatrix_apply, hrow, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  unfold dU
  rw [(β.form U).eq_smul_basis_det e]
  simp only [AlternatingMap.smul_apply, Module.Basis.det_apply, hM, Matrix.det_mul, Matrix.det_transpose, smul_eq_mul]
  ring

variable [Finite k] {C : Type} [AddCommGroup C]

open Classical in

def univTerm (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k) (U : Planes k r n) :
    AddMonoidAlgebra ℚ C :=
  if h : Compl U.1 y then
    AddMonoidAlgebra.single (Multiplicative.toAdd (κ (Units.mk0 _ ((dU_ne_zero_iff β U y).2 h)))) 1
  else 0

def univ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k) : AddMonoidAlgebra ℚ C :=
  haveI := Fintype.ofFinite (Planes k r n)
  ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ • ∑ U : Planes k r n, univTerm β κ y U

def univCoef (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (c : C) (y : Matrix (Fin r) (Fin n) k) : ℚ :=
  (univ β κ y).coeff c

theorem univCoef_eq (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (c : C) (y : Matrix (Fin r) (Fin n) k) :
    univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      Nat.card {U : Planes k r n // ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c} := by
  classical
  haveI := Fintype.ofFinite (Planes k r n)
  have hterm : ∀ U : Planes k r n, (univTerm β κ y U).coeff c =
      if ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases hC : Compl U.1 y
    · rw [dif_pos hC, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases hE : ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c
      · obtain ⟨u, hu, hc⟩ := hE
        have hmk : Units.mk0 _ ((dU_ne_zero_iff β U y).2 hC) = u := Units.ext (by simp [hu])
        rw [hmk, if_pos hc, if_pos ⟨u, hu, hc⟩]
      · rw [if_neg hE, if_neg]
        exact fun hc => hE ⟨_, rfl, hc⟩
    · rw [dif_neg hC, if_neg, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      rintro ⟨u, hu, -⟩
      exact hC ((dU_ne_zero_iff β U y).1 (hu ▸ u.ne_zero))
  unfold univCoef univ
  rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp_rw [hterm]
  clear hterm
  rw [Finset.sum_boole, smul_eq_mul]
  congr 2
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun U => by simp)

structure IsAdmissible (κ : kˣ →* Multiplicative C) (Φ : C → Matrix (Fin r) (Fin n) k → ℚ) : Prop where
  den : ∀ c y, ∃ (m : ℕ) (z : ℤ), Φ c y * (Nat.card k : ℚ) ^ m = z
  equiv : ∀ (g : GL (Fin r) k) c y,
    Φ c (((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * y) =
      Φ (c + Multiplicative.toAdd (κ (GeneralLinearGroup.det g))) y

theorem isAdmissible_univCoef (β : DetBases k r n) (κ : kˣ →* Multiplicative C) : IsAdmissible κ (univCoef β κ) where
  den c y := by
    have hq : (Nat.card k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    refine ⟨r * (n - r), Nat.card {U : Planes k r n // ∃ u : kˣ, (u : k) = dU β U y ∧ Multiplicative.toAdd (κ u) = c}, ?_⟩
    rw [univCoef_eq, mul_comm, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
    simp
  equiv g c y := by
    rw [univCoef_eq, univCoef_eq]
    congr 2
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro U
    set a := GeneralLinearGroup.det g
    have hd : dU β U (((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * y) = ((a⁻¹ : kˣ) : k) * dU β U y := by
      rw [dU_mul]
      congr 1
    rw [hd]
    constructor
    · rintro ⟨u, hu, hc⟩
      refine ⟨a * u, ?_, ?_⟩
      · rw [Units.val_mul, hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      · rw [map_mul, toAdd_mul, hc, add_comm]
    · rintro ⟨u, hu, hc⟩
      refine ⟨a⁻¹ * u, ?_, ?_⟩
      · rw [Units.val_mul, hu]
      · rw [map_mul, toAdd_mul, hc, map_inv, toAdd_inv]
        abel

theorem univ_of_not_linearIndependent (β : DetBases k r n) (κ : kˣ →* Multiplicative C) {y : Matrix (Fin r) (Fin n) k}
    (h : ¬ LinearIndependent k y.row) : univ β κ y = 0 := by
  have hz : ∀ U : Planes k r n, univTerm β κ y U = 0 := by
    intro U
    have hd : dU β U y = 0 :=
      (β.form U).map_linearDependent _ fun hli => h (LinearIndependent.of_comp U.1.mkQ hli)
    have hc : ¬ Compl U.1 y := fun hc => (dU_ne_zero_iff β U y).2 hc hd
    unfold univTerm
    rw [dif_neg hc]
  unfold univ
  simp [hz]

end Univ

example {k : Type} [Field k] (ν : kˣ →* ℂˣ) : flat ν (!![1, 0] : Matrix (Fin 1) (Fin 2) k) = 1 := by
  rw [flat_of_isUnit ν (u := 1) (by simp [topL])]; simp

example {k : Type} [Field k] (ν : kˣ →* ℂˣ) (a : kˣ) (b : k) :
    flat ν (!![(a : k), b] : Matrix (Fin 1) (Fin 2) k) = ν a :=
  flat_of_isUnit ν (by simp [topL])

example {k : Type} [Field k] (ν : kˣ →* ℂˣ) : flat ν (!![0, 1] : Matrix (Fin 1) (Fin 2) k) = 0 :=
  flat_of_not_isUnit ν (by simp [topL])

end GlobalTheory.ExportSeries

end
