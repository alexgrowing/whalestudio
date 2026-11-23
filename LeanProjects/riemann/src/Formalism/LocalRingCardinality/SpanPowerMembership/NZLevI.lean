import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevH

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0)

theorem isUnit_two_W (v : Fin P.nV) : IsUnit (2 : P.W v) := by
  have hirr := (P.setting v).p_unif
  by_contra h
  have hmax : (2 : P.W v) ∈ IsLocalRing.maximalIdeal (P.W v) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr, Ideal.mem_span_singleton] at hmax
  obtain ⟨y, hy⟩ := hmax
  have hodd : Odd p := (P.setting v).prime.odd_of_ne_two (by have := (P.setting v).five_le; omega)
  obtain ⟨k, hk⟩ := hodd
  have h1 : (1 : P.W v) = (p : P.W v) * (1 - y * k) := by
    have h0 : ((p : ℕ) : P.W v) = ((2 * k + 1 : ℕ) : P.W v) := congrArg _ hk
    have : ((p : ℕ) : P.W v) = 2 * k + 1 := by rw [h0]; push_cast; ring
    calc (1 : P.W v) = (p : P.W v) - 2 * k := by rw [this]; ring
      _ = _ := by rw [hy]; ring
  exact hirr.not_isUnit (IsUnit.of_mul_eq_one _ h1.symm)

theorem alg_units_zpow (u : Oˣ) (z : ℤ) : algebraMap O Kf ((u ^ z : Oˣ) : O) = (algebraMap O Kf (u : O)) ^ z := by
  have h1 : algebraMap O Kf ((u ^ z : Oˣ) : O) = ((Units.map (algebraMap O Kf).toMonoidHom (u ^ z) : Kfˣ) : Kf) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

def dT (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) (v : Fin P.nV) : Fin (P.m + 1) → P.Qq v :=
  fun a => if v = v0 ∧ a = a0 then 2 else 1

theorem two_ne (v : Fin P.nV) : (2 : P.Qq v) ≠ 0 := by
  haveI := (P.setting v).frac_alt
  have := (isUnit_two_W P v).map (algebraMap (P.W v) (P.Qq v))
  rw [map_ofNat] at this
  exact this.ne_zero

theorem dT_ne (v0 a0 v) (a : Fin (P.m + 1)) : dT P v0 a0 v a ≠ 0 := by
  unfold dT; split_ifs
  · exact two_ne P v
  · exact one_ne_zero

def torM (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) (v : Fin P.nV) : GL (Fin (P.m + 1)) (P.Qq v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (dT P v0 a0 v))
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun a _ => dT_ne P v0 a0 v a)

theorem torM_inv (v0 a0 v) : (((torM P v0 a0 v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix _ _ _) =
    Matrix.diagonal fun a => (dT P v0 a0 v a)⁻¹ := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_left_inv ?_
  show Matrix.diagonal _ * Matrix.diagonal (dT P v0 a0 v) = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; exact inv_mul_cancel₀ (dT_ne P v0 a0 v a)

theorem gPos_diagonal (v : Fin P.nV) (s : Fin (P.n' v)) (e : Fin (P.m + 1) → P.Qq v) :
    P.gPos v s (Matrix.diagonal e) = Matrix.diagonal fun a => P.ι v ((P.σ v ^ s.val) (e a)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Places.gPos]
  · simp [Places.gPos, Matrix.diagonal_apply_ne _ h]

theorem natAct_tor (v0 a0) : ∃ c : Kf, IsZPow 2 c ∧ P.natAct (torM P v0 a0) = c • (P.subst (Gtor P v0 a0)).toLinearMap := by
  refine ⟨∏ v, ∏ s : Fin (P.n' v), (P.gPos v s (torM P v0 a0 v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det ^
      (-(lamAt (P.lam0 v) s (Fin.last P.m))), IsZPow.prod two_ne_zero _ _ fun v _ => IsZPow.prod two_ne_zero _ _ fun s _ => ?_, ?_⟩
  · refine IsZPow.zpow ?_ _
    show IsZPow 2 (P.gPos v s (Matrix.diagonal (dT P v0 a0 v))).det
    rw [gPos_diagonal, Matrix.det_diagonal]
    refine IsZPow.prod two_ne_zero _ _ fun a _ => ?_
    unfold dT; split_ifs
    · exact ⟨1, by rw [zpow_one, map_ofNat, map_ofNat]⟩
    · exact ⟨0, by rw [zpow_zero, map_one, map_one]⟩
  · unfold Places.natAct
    congr 2
    congr 1
    funext v s
    rw [torM_inv, gPos_diagonal]
    unfold Gtor dT
    congr 1; funext a
    split_ifs
    · rw [map_inv₀, map_inv₀, map_ofNat, map_ofNat]
    · rw [inv_one, map_one, map_one]

theorem EV_isWH : IsWeightedHomogeneous (om P) (EV P) (LamTot P) := by
  refine prodF_isWH P _ _ fun v s => ?_
  have h := hwRowWeight Kf (P.m + 1) (P.m + 1) le_rfl (nuV P v s) (nuV_anti P v s)
  have : rowNu (r := P.m + 1) (nuV P v s) = nuV P v s := by funext a; unfold rowNu; rw [dif_pos a.2]
  rwa [this] at h

theorem subst_Gtor_EV (v0 a0) :
    P.subst (Gtor P v0 a0) (EV P) = ((2 : Kf)⁻¹ ^ (LamTot P (v0, a0))) • EV P := by
  ext m
  rw [subst_Gtor, coeff_aeval_scale, prod_tor, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m (EV P) = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [EV_isWH P hm]

theorem tor_mem (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) :
    ∃ u : Oˣ, (torM P v0 a0, u) ∈ Γsub P hp ∧
      P.natAct (torM P v0 a0) (EV P) = algebraMap O Kf ((u⁻¹ : Oˣ) : O) • EV P := by
  obtain ⟨c, ⟨N, rfl⟩, hc⟩ := natAct_tor P v0 a0
  have h2O : IsUnit (2 : O) := by
    have := (isUnit_two_W P v0).map (P.j v0); rwa [map_ofNat] at this
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (2 : Kf) ^ N * (2 : Kf)⁻¹ ^ (LamTot P (v0, a0)) = (2 : Kf) ^ M :=
    ⟨N - LamTot P (v0, a0), by rw [zpow_sub₀ two_ne_zero, zpow_natCast, div_eq_mul_inv, inv_pow]⟩
  refine ⟨h2O.unit ^ (-M), ?_, ?_⟩ <;>
  · have : P.natAct (torM P v0 a0) (EV P) = algebraMap O Kf ((((h2O.unit ^ (-M))⁻¹ : Oˣ)) : O) • EV P := by
      rw [hc, LinearMap.smul_apply, AlgHom.toLinearMap_apply, subst_Gtor_EV, smul_smul, hM, zpow_neg, inv_inv,
        alg_units_zpow, IsUnit.unit_spec, map_ofNat]
    first
    | exact ⟨0, by rw [this, zpow_zero, one_mul]⟩
    | exact this

theorem tor_stab (v0 a0) (u : Oˣ) (hu : (torM P v0 a0, u) ∈ Γsub P hp) :
    (levB P hp).smul ⟨(torM P v0 a0, u), hu⟩ (standardTuple P) = standardTuple P := by
  funext v
  show Formalism.L2.G.Cmp.gMap (P.W v) (torM P v0 a0 v) (Formalism.L2.G.Cmp.stdL (P.W v)) = Formalism.L2.G.Cmp.stdL (P.W v)
  haveI := (P.setting v).frac_alt
  refine (Formalism.L2.G.Cmp.stabStd_iff (P.W v) _).mpr ⟨fun a b => ?_, fun a b => ?_⟩
  · show Matrix.diagonal (dT P v0 a0 v) a b ∈ _
    by_cases h : a = b
    · subst h; rw [Matrix.diagonal_apply_eq]; unfold dT; split_ifs
      · exact ⟨2, map_ofNat _ 2⟩
      · exact ⟨1, map_one _⟩
    · rw [Matrix.diagonal_apply_ne _ h]; exact Subring.zero_mem _
  · rw [torM_inv]
    by_cases h : a = b
    · subst h; rw [Matrix.diagonal_apply_eq]; unfold dT; split_ifs
      · refine ⟨((isUnit_two_W P v).unit⁻¹ : (P.W v)ˣ), ?_⟩
        have h1 := congrArg (algebraMap (P.W v) (P.Qq v)) ((isUnit_two_W P v).unit.inv_mul)
        rw [map_mul, IsUnit.unit_spec, map_ofNat, map_one] at h1
        exact eq_inv_of_mul_eq_one_left h1
      · exact ⟨1, by simp⟩
    · rw [Matrix.diagonal_apply_ne _ h]; exact Subring.zero_mem _

end Formalism.BasicNotions.Examples₂.NZ
