import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open UpperTheory.V.Z.Desc.V0

noncomputable section

open GlobalTheory.SmGL Matrix

namespace UpperTheory.V.Z.Desc.V0.KirillovTranslation

variable {k : Type} [Field k] {n : ℕ}

private def dg (e : Fin n → k) (he : ∀ i, e i ≠ 0) : GeneralLinearGroup (Fin n) k :=
  ⟨diagonal e, diagonal fun i => (e i)⁻¹, by simp [diagonal_mul_diagonal, he, ← diagonal_one],
    by simp [diagonal_mul_diagonal, he, ← diagonal_one]⟩

private theorem dg_inv_val (e : Fin n → k) (he : ∀ i, e i ≠ 0) :
    (((dg e he)⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal fun i => (e i)⁻¹ := rfl

private theorem dg_val (e : Fin n → k) (he : ∀ i, e i ≠ 0) :
    ((dg e he : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal e := rfl

private theorem conj_apply (e : Fin n → k) (he : ∀ i, e i ≠ 0) (u : GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    ((dg e he * u * (dg e he)⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      e i * (u : Matrix (Fin n) (Fin n) k) i j * (e j)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, dg_inv_val, dg_val, mul_diagonal, diagonal_mul]

private theorem inv_mul_apply (e : Fin n → k) (he : ∀ i, e i ≠ 0) (p : GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    (((dg e he)⁻¹ * p : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (e i)⁻¹ * (p : Matrix (Fin n) (Fin n) k) i j := by
  rw [Units.val_mul, dg_inv_val, diagonal_mul]

private def ee (c : Fin n → k) (i : Fin n) : k :=
  ∏ j : Fin n with i ≤ j ∧ (j : ℕ) + 1 < n, c j

private theorem ee_ne (c : Fin n → k) (hc : ∀ i, c i ≠ 0) (i : Fin n) : ee c i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => hc j

private theorem ee_last (c : Fin n → k) (i : Fin n) (hi : (i : ℕ) + 1 = n) : ee c i = 1 := by
  unfold ee
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hj
  omega

private theorem ee_step (c : Fin n → k) (i j : Fin n) (hij : (j : ℕ) = i + 1) : ee c i = c i * ee c j := by
  unfold ee
  have hi : i ∈ (Finset.univ.filter fun x : Fin n => i ≤ x ∧ (x : ℕ) + 1 < n) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
    have := j.isLt
    omega
  rw [← Finset.mul_prod_erase _ _ hi]
  congr 1
  apply Finset.prod_congr
  · ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, ne_eq, Fin.ext_iff]
    omega
  · intro _ _
    rfl

end UpperTheory.V.Z.Desc.V0.KirillovTranslation

open UpperTheory.V.Z.Desc.V0.KirillovTranslation in
theorem UpperTheory.V.Z.Desc.V0.kirMove :
    KirMove := by
  intro k _ _ _ _ n W _ _ τ hK ψ t hψ hψ1 ht
  obtain ⟨ψ0, l0, hc0, hn0, hu0, hm0⟩ := hK
  obtain ⟨a, ha⟩ := GlobalTheory.LocGL.exists_unit_eq_mulShift hc0 hn0 hψ hψ1
  let c : Fin n → k := fun i => (a : k) * t i
  have hcE : ∀ i, c i = (a : k) * t i := fun _ => rfl
  have hc : ∀ i, c i ≠ 0 := fun i => mul_ne_zero a.ne_zero (ht i)
  let g : GeneralLinearGroup (Fin n) k := dg (ee c) (ee_ne c hc)
  have hτ : ∀ (x y : GeneralLinearGroup (Fin n) k) (w : W), τ (x * y) w = τ x (τ y w) := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨l0 ∘ₗ τ g, ?_, ?_⟩
  · intro u hu v
    have hconj : g * u * g⁻¹ ∈ unipB k (Fin n) := by
      rw [mem_unipB] at hu ⊢
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · rw [conj_apply, hu.1 i j hji, mul_zero, zero_mul]
      · rw [conj_apply, hu.2 i, mul_one, mul_inv_cancel₀ (ee_ne c hc i)]
    have hmove : τ g (τ u v) = τ (g * u * g⁻¹) (τ g v) := by
      rw [hτ, hτ, ← hτ g⁻¹, inv_mul_cancel, map_one, Module.End.one_apply]
    simp only [LinearMap.comp_apply]
    rw [hmove, hu0 _ hconj]
    congr 1
    unfold chr
    rw [ha, AddChar.mulShift_apply, Finset.mul_sum]
    have hs : (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
        (fun _ => (1 : k)) p.1 * ((g * u * g⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
          (a : k) * (t p.1 * (u : Matrix (Fin n) (Fin n) k) p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [conj_apply, ee_step c p.1 p.2 hp, hcE]
      have hE := ee_ne c hc p.2
      field_simp
    rw [hs]
  · intro v hv
    apply hm0 v
    intro q hq
    have hp : IsMirL (g⁻¹ * q) := by
      intro i j hi
      rw [inv_mul_apply, ee_last c i hi, inv_one, one_mul]
      exact hq i j hi
    have := hv _ hp
    simp only [LinearMap.comp_apply] at this
    rwa [← hτ, mul_inv_cancel_left] at this
