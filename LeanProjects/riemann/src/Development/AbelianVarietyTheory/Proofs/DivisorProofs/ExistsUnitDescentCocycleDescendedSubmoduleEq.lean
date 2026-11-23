import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicCech

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem exists_sum_of_mem_mul {M N : Submodule A B} {z : B} (hz : z ∈ M * N) :
    ∃ (ι : Type) (_ : Fintype ι) (x y : ι → B), (∀ i, x i ∈ M) ∧ (∀ i, y i ∈ N) ∧ ∑ i, x i * y i = z := by
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem m hm n hn => exact ⟨Unit, inferInstance, fun _ => m, fun _ => n, fun _ => hm, fun _ => hn, by simp⟩
  | add a _ b _ ha hb =>
    obtain ⟨ι, _, x, y, hx, hy, hs⟩ := ha
    obtain ⟨κ, _, x', y', hx', hy', hs'⟩ := hb
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim x x', Sum.elim y y', ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp [hx, hx']
    · rintro (i | i) <;> simp [hy, hy']
    · rw [Fintype.sum_sum_type]; simp [hs, hs']

theorem tmul_eq_one_tmul {c : B} (hc : c ∈ (1 : Submodule A B)) (q : B) :
    c ⊗ₜ[A] q = (1 : B) ⊗ₜ[A] (c * q) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem tmul_eq_tmul_one {c : B} (hc : c ∈ (1 : Submodule A B)) (p : B) :
    p ⊗ₜ[A] c = (p * c) ⊗ₜ[A] (1 : B) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hc
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

theorem sum_tmul_mul_one_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1) {b : B}
    (hb : ∀ i, y i * b ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := by
  rw [Finset.sum_mul]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => tmul_eq_tmul_one (hb i) (x i)), ← TensorProduct.sum_tmul]
  congr 1
  simp_rw [← mul_assoc]; rw [← Finset.sum_mul, hs, one_mul]

theorem sum_tmul_mul_sum_tmul {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B)) :
    (∑ i, x i ⊗ₜ[A] y i) * (∑ j, y j ⊗ₜ[A] x j) = 1 := by
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => tmul_eq_one_tmul (hxy i j) (y i * x j)))]
  simp_rw [← TensorProduct.tmul_sum]
  rw [Algebra.TensorProduct.one_def]
  congr 1
  calc ∑ i, ∑ j, x i * y j * (y i * x j) = (∑ i, x i * y i) * (∑ j, x j * y j) := by
        rw [Finset.sum_mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 1 := by rw [hs, one_mul]

theorem cocycle_sum {ι : Type} [Fintype ι] (x y : ι → B) (hs : ∑ i, x i * y i = 1)
    (hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B)) :
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) =
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) (∑ i, x i ⊗ₜ[A] y i) *
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (∑ i, x i ⊗ₜ[A] y i) := by
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeLeft_apply]
  rw [Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun t => x i ⊗ₜ[A] t) (tmul_eq_one_tmul (hyx i j) (y j))))]
  simp_rw [← TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum, hs, mul_one]

theorem exists_unitCocycle_descMod_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], descMod A B 1 ≤ 1 →
    ∀ I : (Submodule A B)ˣ, ∃ u : (B ⊗[A] B)ˣ, UCoc A B u ∧ descMod A B u = (I : Submodule A B) := by
  intro A B _ _ _ h1 I
  have hone : (1 : B) ∈ (I : Submodule A B) * ↑I⁻¹ := by
    rw [I.mul_inv]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨ι, _, x, y, hx, hy, hs⟩ := exists_sum_of_mem_mul hone
  have hxy : ∀ i j, x i * y j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.mul_inv]; exact Submodule.mul_mem_mul (hx i) (hy j)
  have hyx : ∀ i j, y i * x j ∈ (1 : Submodule A B) := fun i j => by
    rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) (hx j)
  have hs' : ∑ i, y i * x i = 1 := by simp_rw [mul_comm (y _)]; exact hs
  have huv := sum_tmul_mul_sum_tmul x y hs hxy
  let u : (B ⊗[A] B)ˣ := ⟨∑ i, x i ⊗ₜ[A] y i, ∑ j, y j ⊗ₜ[A] x j, huv, by rw [mul_comm]; exact huv⟩
  refine ⟨u, cocycle_sum x y hs hyx, le_antisymm ?_ ?_⟩
  · intro b hb
    have hb' : (∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b) = b ⊗ₜ[A] (1 : B) := hb
    have key : ∀ i, b * y i ∈ (1 : Submodule A B) := by
      intro i
      apply h1
      show ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i)) = (b * y i) ⊗ₜ[A] (1 : B)
      have hv := sum_tmul_mul_one_tmul y x hs' (b := y i) (fun j => hxy j i)
      calc ((1 : (B ⊗[A] B)ˣ) : B ⊗[A] B) * ((1 : B) ⊗ₜ[A] (b * y i))
          = ((∑ i, x i ⊗ₜ[A] y i) * ((1 : B) ⊗ₜ[A] b)) * ((∑ j, y j ⊗ₜ[A] x j) * ((1 : B) ⊗ₜ[A] y i)) := by
            rw [mul_mul_mul_comm, huv, Algebra.TensorProduct.tmul_mul_tmul, Units.val_one, one_mul, one_mul, one_mul]
        _ = (b * y i) ⊗ₜ[A] (1 : B) := by rw [hb', hv, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hb2 : b = ∑ i, (b * y i) * x i := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hs', mul_one]
    rw [hb2]
    exact Submodule.sum_mem _ fun i _ => by simpa using Submodule.mul_mem_mul (key i) (hx i)
  · intro b hb
    exact sum_tmul_mul_one_tmul x y hs (fun i => by rw [← I.inv_mul]; exact Submodule.mul_mem_mul (hy i) hb)

end GlobalTheory.PicCech
