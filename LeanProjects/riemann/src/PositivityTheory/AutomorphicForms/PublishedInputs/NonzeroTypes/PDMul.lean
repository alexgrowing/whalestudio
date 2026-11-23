import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_DMul

theorem minor_mul_sub_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (Q : Ideal R) (A B : Matrix ι ι R) (hB : ∀ i j, ¬ p i → p j → B i j ∈ Q) :
    ((A * B).submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det -
      (A.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det *
        (B.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det ∈ Q := by
  rw [← Ideal.Quotient.eq, RingHom.map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, ← det_mul]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.mul_apply, map_sum, map_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ l : {x // ¬ p x}, (Ideal.Quotient.mk Q) (A i l) * (Ideal.Quotient.mk Q) (B l j) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hB l j l.2 j.2), mul_zero]
  rw [h0, add_zero]

theorem minor_isUnit {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (M : Matrix ι ι R) (hM : IsUnit M.det) (hl : ∀ i j, ¬ p i → p j → M i j ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det := by
  have ht := twoBlockTriangular_det ((IsLocalRing.residue R).mapMatrix M) p
    (fun i hi j hj => (IsLocalRing.residue_eq_zero_iff _).mpr (hl i j hi hj))
  rw [← RingHom.map_det] at ht
  have hu : IsUnit ((IsLocalRing.residue R) M.det) := hM.map _
  rw [ht] at hu
  have h1 := isUnit_of_mul_isUnit_left hu
  refine IsUnit.of_map (IsLocalRing.residue R) _ ?_
  rw [RingHom.map_det]
  exact h1

theorem unit_factor {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (x y z : R) (hy : IsUnit y) (hz : IsUnit z) (hxyz : x - y * z ∈ Q) :
    ∃ u : Rˣ, (u : R) - 1 ∈ Q ∧ x = y * z * u := by
  obtain ⟨W, hW⟩ : IsUnit (y * z) := hy.mul hz
  have hsub : x * ((W⁻¹ : Rˣ) : R) - 1 ∈ Q := by
    have e : x * ((W⁻¹ : Rˣ) : R) - 1 = (x - y * z) * ((W⁻¹ : Rˣ) : R) := by
      rw [sub_mul, ← hW, Units.mul_inv]
    rw [e]
    exact Ideal.mul_mem_right _ _ hxyz
  have hunit : IsUnit (x * ((W⁻¹ : Rˣ) : R)) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (hQ hsub)
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hsub
  · rw [IsUnit.unit_spec, ← hW, mul_left_comm, Units.mul_inv, mul_one]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem low {n : ℕ} (G : Grp k n) (a : Fin G.s) (h1 : (a : ℕ) + 1 < G.s) (X : GL (Fin n) 𝒪[k])
    (x : GL (Fin n) k) (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) (hx : x ∈ G.JSet)
    (i j : Fin n) (hi : ¬ (G.bl i ≤ a)) (hj : G.bl j ≤ a) :
    (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ := by
  have hlt : G.bl j < G.bl i := lt_of_le_of_lt hj (not_le.mp hi)
  obtain ⟨y, hy, hyx⟩ := hx.2 i j hlt
  have hyX : y = (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
    apply FaithfulSMul.algebraMap_injective 𝒪[k] k
    rw [hyx, ← hX]
    rfl
  rw [← hyX]
  have hia : (a : ℕ) < (G.bl i : ℕ) := not_le.mp hi
  have hle : cc G.μ a ⟨a + 1, h1⟩ ≤ cc G.μ (G.bl j) (G.bl i) :=
    G.ball (G.bl j) a ⟨a + 1, h1⟩ (G.bl i) hj (Fin.lt_def.mpr (Nat.lt_succ_self _)) (Fin.le_def.mpr hia)
  exact Ideal.pow_le_pow_right hle hy

theorem delta_eq {n : ℕ} (G : Grp k n) (a : Fin G.s) (X : Matrix (Fin n) (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hx : (x : Matrix (Fin n) (Fin n) k) = X.map (algebraMap 𝒪[k] k)) :
    G.Δ a x = algebraMap 𝒪[k] k (X.submatrix (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  unfold Grp.Δ
  rw [hx, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_eq {n : ℕ} (X : GL (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) :
    (x : Matrix (Fin n) (Fin n) k) = (X : Matrix (Fin n) (Fin n) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
  rw [← hX]; rfl

end UpperTheory.TNZ.Grp.P_DMul

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_DMul {n : ℕ} (G : Grp k n) : ModulusMultiplicativeProp G := by
  intro _ hB g hg h hh a h1
  have hab : a ≠ ⟨a + 1, h1⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  have hc1 : 1 ≤ cc G.μ a ⟨a + 1, h1⟩ := hB.1 a _ hab
  have hQ : IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal 𝒪[k]) hc1
    rwa [pow_one] at this
  obtain ⟨G', hG'⟩ := hg.1
  obtain ⟨H', hH'⟩ := hh.1
  have uG := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp G'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 G' g hG' hg i j hi hj))
  have uH := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp H'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 H' h hH' hh i j hi hj))
  have key := P_DMul.minor_mul_sub_mem (fun i => G.bl i ≤ a) _ (G' : Matrix (Fin n) (Fin n) 𝒪[k]) _
    (P_DMul.low G a h1 H' h hH' hh)
  obtain ⟨u, hu1, hu2⟩ := P_DMul.unit_factor _ hQ _ _ _ uG uH key
  refine ⟨u, hu1, ?_⟩
  have hgm := P_DMul.coe_map_eq G' g hG'
  have hhm := P_DMul.coe_map_eq H' h hH'
  have hghm : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((G' : Matrix (Fin n) (Fin n) 𝒪[k]) * (H' : Matrix (Fin n) (Fin n) 𝒪[k])).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, hgm, hhm, Matrix.map_mul]
  rw [P_DMul.delta_eq G a _ _ hghm, P_DMul.delta_eq G a _ _ hgm, P_DMul.delta_eq G a _ _ hhm, ← map_mul, ← map_mul]
  exact congrArg _ hu2

end UpperTheory.TNZ.Grp
