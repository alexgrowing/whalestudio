import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

open Matrix Module ValuativeRel GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isClosed_Gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Gz Z : Set (GL (Fin n) k)) := by
  have : (Gz Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g; simp [Gz]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

private theorem exists_uniformizer_pow_mul_valuation_le_one (a : k) : ∃ e : ℕ,
    valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e * valuation k a ≤ 1 := by
  by_cases ha : valuation k a ≤ 1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact ha⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero]; exact zero_le')
  have hinv : valuation k a⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))
  set b : 𝒪[k] := ⟨a⁻¹, hinv⟩ with hb
  have hb0 : b ≠ 0 := by
    intro h
    have h' : (b : k) = 0 := by rw [h]; rfl
    exact inv_ne_zero ha0 h'
  have hirr : Irreducible (GroundTheory.Automorphic.GLnLocal.uniformizer k) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    exact h
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr
  refine ⟨e, ?_⟩
  have h1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e ≤ valuation k a⁻¹ := by
    have h2 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e = a⁻¹ * ((u : 𝒪[k]) : k) := by
      have h3 := congrArg (fun z : 𝒪[k] => (z : k)) hu
      simpa [hb] using h3.symm
    rw [← map_pow, h2, map_mul]
    calc _ ≤ valuation k a⁻¹ * 1 := mul_le_mul_right (u : 𝒪[k]).2 _
      _ = _ := mul_one _
  calc _ ≤ valuation k a⁻¹ * valuation k a := mul_le_mul_left h1 _
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]

private theorem mul_mul_apply_mem_integers_of_valuation_bounds (E : ℕ) (P Q y : Matrix (Fin n) (Fin n) k)
    (hP : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (P i j) ≤ 1)
    (hQ : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (Q i j) ≤ 1)
    (hy : ∀ i j, valuation k (y i j) ≤ valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E)
    (i j : Fin n) : (P * y * Q) i j ∈ 𝒪[k] := by
  set c := valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E with hc
  rw [Matrix.mul_apply]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun a _ => ?_
  show valuation k (P i a * y a b * Q b j) ≤ 1
  rw [map_mul, map_mul]
  calc valuation k (P i a) * valuation k (y a b) * valuation k (Q b j)
      ≤ valuation k (P i a) * (c * c) * valuation k (Q b j) :=
        mul_le_mul_left (mul_le_mul_right (hy a b) _) _
    _ = (c * valuation k (P i a)) * (c * valuation k (Q b j)) := by ac_rfl
    _ ≤ 1 * 1 := mul_le_mul' (hP i a) (hQ b j)
    _ = 1 := one_mul 1

theorem exists_level (g : GL (Fin n) k) : ∃ m : ℕ, 1 ≤ m ∧ ∀ u ∈ congruenceSubgroup k n m,
    g⁻¹ * u * g ∈ integralGL k n ∧ g * u * g⁻¹ ∈ integralGL k n := by
  classical
  choose e he using fun a : k => exists_uniformizer_pow_mul_valuation_le_one (k := k) a
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hA
  set B : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hB
  set E : ℕ := ∑ i, ∑ j, (e (A i j) + e (B i j)) with hE
  have hπ1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≤ 1 :=
    (GroundTheory.Automorphic.GLnLocal.uniformizer k).2
  have hbound : ∀ a : k, e a ≤ E →
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k a ≤ 1 := by
    intro a ha
    exact le_trans (mul_le_mul_left (pow_le_pow_right_of_le_one' hπ1 ha) _) (he a)
  have hrow : ∀ i j, e (A i j) + e (B i j) ≤ E := by
    intro i j
    calc e (A i j) + e (B i j) ≤ ∑ j', (e (A i j') + e (B i j')) :=
          Finset.single_le_sum (f := fun j' => e (A i j') + e (B i j'))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ E := Finset.single_le_sum (f := fun i' => ∑ j', (e (A i' j') + e (B i' j')))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have heA : ∀ i j, e (A i j) ≤ E := fun i j => le_trans (Nat.le_add_right _ _) (hrow i j)
  have heB : ∀ i j, e (B i j) ≤ E := fun i j => le_trans (Nat.le_add_left _ _) (hrow i j)
  have hBA : B * A = 1 := Units.inv_mul g
  have hAB : A * B = 1 := Units.mul_inv g
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨2 * E + 1, by omega, ?_⟩
  have hconj : ∀ w ∈ congruenceSubgroup k n (2 * E + 1), ∀ i j,
      ((g⁻¹ * w * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] ∧
      ((g * w * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro w hw i j
    rw [mem_congruenceSubgroup_iff] at hw
    set y : Matrix (Fin n) (Fin n) k := (w : Matrix (Fin n) (Fin n) k) - 1 with hy
    have hw' : (w : Matrix (Fin n) (Fin n) k) = 1 + y := by rw [hy]; abel
    have hyb : ∀ a b, valuation k (y a b) ≤
        valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E := by
      intro a b
      rw [← pow_add]
      exact le_trans (hw.2 a b) (pow_le_pow_right_of_le_one' hπ1 (by omega))
    constructor
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hBA, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E B A y (fun i j => hbound _ (heB i j))
        (fun i j => hbound _ (heA i j)) hyb i j)
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hAB, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E A B y (fun i j => hbound _ (heA i j))
        (fun i j => hbound _ (heB i j)) hyb i j)
  intro u hu
  refine ⟨?_, ?_⟩
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).1, fun i j => ?_⟩
    have hinv : (g⁻¹ * u * g)⁻¹ = g⁻¹ * u⁻¹ * g := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).1
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).2, fun i j => ?_⟩
    have hinv : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).2

theorem exists_unit (m : ℕ) (hm : 1 ≤ m) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ i j, valuation k (x i j) ≤ valuation k (uniformizer k : k) ^ m) :
    ∃ u ∈ congruenceSubgroup k n m, u.val = 1 + x := by
  classical
  set π := GroundTheory.Automorphic.GLnLocal.uniformizer k with hπ
  have hπm : π ∈ 𝓂[k] := by
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    rw [h]
    exact Ideal.subset_span rfl
  have hπ1 : valuation k (π : k) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hπm
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπm
  have hle : ∀ i j, valuation k (x i j) < 1 := fun i j =>
    lt_of_le_of_lt (hx i j) (pow_lt_one₀ zero_le' hπ1 (by omega))
  let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x i j, (hle i j).le⟩
  have hXm : ∀ i j, X i j ∈ 𝓂[k] := fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (hle i j)
  have hdet : IsUnit (1 + X).det := by
    have h1 : (IsLocalRing.residue 𝒪[k]) (1 + X).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      have h0 : X.map (IsLocalRing.residue 𝒪[k]) = 0 := by
        ext i j
        simpa [IsLocalRing.residue_eq_zero_iff] using hXm i j
      rw [h0, add_zero, Matrix.det_one]
    by_contra h
    have hm : (1 + X).det ∈ IsLocalRing.maximalIdeal 𝒪[k] := h
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at h1
    exact zero_ne_one h1
  have hU : IsUnit (1 + X) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hentry : ∀ i j, (((1 + X) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j + x i j := by
    intro i j
    show (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) + x i j = _
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨integralGLHom k n hU.unit, ?_, ?_⟩
  · rw [mem_congruenceSubgroup_iff]
    refine ⟨⟨hU.unit, rfl⟩, fun i j => ?_⟩
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, add_sub_cancel_left]
    exact hx i j
  · ext i j
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, Matrix.add_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
