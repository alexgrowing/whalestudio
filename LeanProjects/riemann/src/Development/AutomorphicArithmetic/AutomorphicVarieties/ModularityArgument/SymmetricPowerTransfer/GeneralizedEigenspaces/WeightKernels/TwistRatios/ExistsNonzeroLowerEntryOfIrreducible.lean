import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariantSubspaces

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga.S4

variable {k : Type} [Field k]

private theorem eig_vec (A : Matrix (Fin 2) (Fin 2) k) (a b c : k)
    (hc : A.charpoly = (X - C a) * (X - C b)) (hcab : c = a ∨ c = b) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ A.mulVec v = c • v := by
  have hz : (A.charpoly).eval c = 0 := by
    rw [hc]; rcases hcab with rfl | rfl <;> simp
  rw [Matrix.eval_charpoly] at hz
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hz
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem eig_basis (A : Matrix (Fin 2) (Fin 2) k) (a b : k) (hab : a ≠ b)
    (hc : A.charpoly = (X - C a) * (X - C b)) :
    ∃ Q : GL (Fin 2) k, A * (Q : Matrix (Fin 2) (Fin 2) k) = (Q : Matrix (Fin 2) (Fin 2) k) * !![a, 0; 0, b] := by
  obtain ⟨v, hv, hAv⟩ := eig_vec A a b a hc (Or.inl rfl)
  obtain ⟨w, hw, hAw⟩ := eig_vec A a b b hc (Or.inr rfl)
  have v0 := congrFun hAv 0
  have v1 := congrFun hAv 1
  have w0 := congrFun hAw 0
  have w1 := congrFun hAw 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at v0 v1 w0 w1
  have hd : (!![v 0, w 0; v 1, w 1] : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
    intro hd
    obtain ⟨u, hu, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    have e0 : u 1 * w 0 = 0 := by
      have : (b - a) * (u 1 * w 0) = 0 := by
        linear_combination A 0 0 * h0 + A 0 1 * h1 - a * h0 - u 0 * v0 - u 1 * w0
      exact (mul_eq_zero.1 this).resolve_left hba
    have e1 : u 1 * w 1 = 0 := by
      have : (b - a) * (u 1 * w 1) = 0 := by
        linear_combination A 1 0 * h0 + A 1 1 * h1 - a * h1 - u 0 * v1 - u 1 * w1
      exact (mul_eq_zero.1 this).resolve_left hba
    have hu1 : u 1 = 0 := by
      by_contra hu1
      apply hw
      ext i
      fin_cases i
      · exact (mul_eq_zero.1 e0).resolve_left hu1
      · exact (mul_eq_zero.1 e1).resolve_left hu1
    have f0 : u 0 * v 0 = 0 := by rw [hu1] at h0; linear_combination h0
    have f1 : u 0 * v 1 = 0 := by rw [hu1] at h1; linear_combination h1
    have hu0 : u 0 = 0 := by
      by_contra hu0
      apply hv
      ext i
      fin_cases i
      · exact (mul_eq_zero.1 f0).resolve_left hu0
      · exact (mul_eq_zero.1 f1).resolve_left hu0
    apply hu
    ext i
    fin_cases i
    · exact hu0
    · exact hu1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination v0 | linear_combination v1 | linear_combination w0 | linear_combination w1

private theorem exists_nonzero_lower_entry_of_irreducible {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) k) (h : IsIrr r) :
    ∃ x, (r x : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨-, -, hmin⟩ := h
  let W : Submodule k (Fin 2 → k) := LinearMap.ker (LinearMap.proj (1 : Fin 2))
  have hW : ∀ v, v ∈ W ↔ v 1 = 0 := fun v => by simp [W]
  have hinv : IsInv r W := by
    intro x v hv
    rw [hW] at hv ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hno x, hv]
  rcases hmin W le_top hinv with h0 | h1
  · have : (Pi.single 0 1 : Fin 2 → k) ∈ W := by rw [hW]; simp
    rw [h0, Submodule.mem_bot] at this
    simpa using congrFun this 0
  · have : (Pi.single 1 1 : Fin 2 → k) ∈ W := by rw [h1]; trivial
    rw [hW] at this
    simp at this

private theorem exists_nonzero_upper_entry_of_irreducible {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) k) (h : IsIrr r) :
    ∃ x, (r x : Matrix (Fin 2) (Fin 2) k) 0 1 ≠ 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨-, -, hmin⟩ := h
  let W : Submodule k (Fin 2 → k) := LinearMap.ker (LinearMap.proj (0 : Fin 2))
  have hW : ∀ v, v ∈ W ↔ v 0 = 0 := fun v => by simp [W]
  have hinv : IsInv r W := by
    intro x v hv
    rw [hW] at hv ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hno x, hv]
  rcases hmin W le_top hinv with h0 | h1
  · have : (Pi.single 1 1 : Fin 2 → k) ∈ W := by rw [hW]; simp
    rw [h0, Submodule.mem_bot] at this
    simpa using congrFun this 1
  · have : (Pi.single 0 1 : Fin 2 → k) ∈ W := by rw [h1]; trivial
    rw [hW] at this
    simp at this

private theorem inv_mul_gl2_entry_one_zero (A B : GL (Fin 2) k) :
    ((A⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      ((A : Matrix (Fin 2) (Fin 2) k).det)⁻¹ * ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * (B : Matrix (Fin 2) (Fin 2) k) 1 0 -
        (A : Matrix (Fin 2) (Fin 2) k) 1 0 * (B : Matrix (Fin 2) (Fin 2) k) 0 0) := by
  simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem inv_mul_gl2_entry_zero_one (A B : GL (Fin 2) k) :
    ((A⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 =
      ((A : Matrix (Fin 2) (Fin 2) k).det)⁻¹ * ((A : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 0 1 -
        (A : Matrix (Fin 2) (Fin 2) k) 0 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1) := by
  simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem irr_conj {Γ : Type} [Group Γ] {n : ℕ} (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (h : ∀ x, r' x = g * r x * g⁻¹) (hr : IsIrr r') : IsIrr r :=
  _root_.UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.irr_conj r r' g h hr

section Neumann

open scoped Pointwise

variable {H : Type} [Group H]

private def stabilizerLowerTriangular (r : H →* GL (Fin 2) k) : Subgroup H where
  carrier := {x | (r x : Matrix (Fin 2) (Fin 2) k) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have := inv_mul_gl2_entry_one_zero (r x) 1
    simpa [hx] using this

private def stabilizerUpperTriangular (r : H →* GL (Fin 2) k) : Subgroup H where
  carrier := {x | (r x : Matrix (Fin 2) (Fin 2) k) 0 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have := inv_mul_gl2_entry_zero_one (r x) 1
    simpa [hx] using this

private theorem exists_full [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [T1Space k]
    (r : H →* GL (Fin 2) k) (hc : ∀ i j, Continuous fun x => (r x : Matrix (Fin 2) (Fin 2) k) i j)
    (h10 : ∀ K : Subgroup H, IsOpen (K : Set H) → ∃ x ∈ K, (r x : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0)
    (h01 : ∀ K : Subgroup H, IsOpen (K : Set H) → ∃ x ∈ K, (r x : Matrix (Fin 2) (Fin 2) k) 0 1 ≠ 0) :
    ∃ g, ∀ i j, (r g : Matrix (Fin 2) (Fin 2) k) i j ≠ 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨h0, hh0⟩ : ∃ h0 : H, ∀ x, (r x : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 → h0⁻¹ * x ∈ stabilizerLowerTriangular r := by
    by_cases h : ∃ y, (r y : Matrix (Fin 2) (Fin 2) k) 0 0 = 0
    · obtain ⟨y, hy⟩ := h
      refine ⟨y, fun x hx => ?_⟩
      show (r (y⁻¹ * x) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
      rw [map_mul, map_inv, inv_mul_gl2_entry_one_zero, hy, hx]
      ring
    · exact ⟨1, fun x hx => absurd ⟨x, hx⟩ h⟩
  obtain ⟨h1, hh1⟩ : ∃ h1 : H, ∀ x, (r x : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 → h1⁻¹ * x ∈ stabilizerUpperTriangular r := by
    by_cases h : ∃ y, (r y : Matrix (Fin 2) (Fin 2) k) 1 1 = 0
    · obtain ⟨y, hy⟩ := h
      refine ⟨y, fun x hx => ?_⟩
      show (r (y⁻¹ * x) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0
      rw [map_mul, map_inv, inv_mul_gl2_entry_zero_one, hy, hx]
      ring
    · exact ⟨1, fun x hx => absurd ⟨x, hx⟩ h⟩
  have hcov : ⋃ i ∈ (Finset.univ : Finset (Fin 4)), (![1, 1, h0, h1] i : H) • ((![stabilizerLowerTriangular r, stabilizerUpperTriangular r, stabilizerLowerTriangular r, stabilizerUpperTriangular r] i : Subgroup H) : Set H) = Set.univ := by
    have key : ∀ (i : Fin 4) (x : H), (![1, 1, h0, h1] i : H)⁻¹ * x ∈ (![stabilizerLowerTriangular r, stabilizerUpperTriangular r, stabilizerLowerTriangular r, stabilizerUpperTriangular r] i : Subgroup H) →
        x ∈ ⋃ i ∈ (Finset.univ : Finset (Fin 4)), (![1, 1, h0, h1] i : H) • ((![stabilizerLowerTriangular r, stabilizerUpperTriangular r, stabilizerLowerTriangular r, stabilizerUpperTriangular r] i : Subgroup H) : Set H) := by
      intro i x hx
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ i)) ?_
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact hx
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, j, hij⟩ := hno x
    fin_cases i <;> fin_cases j
    · exact key 2 x (by simpa using hh0 x hij)
    · exact key 1 x (by simpa using (show x ∈ stabilizerUpperTriangular r from hij))
    · exact key 0 x (by simpa using (show x ∈ stabilizerLowerTriangular r from hij))
    · exact key 3 x (by simpa using hh1 x hij)
  obtain ⟨i, -, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  have c10 : IsClosed (stabilizerLowerTriangular r : Set H) := isClosed_singleton.preimage (hc 1 0)
  have c01 : IsClosed (stabilizerUpperTriangular r : Set H) := isClosed_singleton.preimage (hc 0 1)
  have n10 : ¬ (stabilizerLowerTriangular r).FiniteIndex := fun hf => by
    obtain ⟨x, hx, hx'⟩ := h10 _ (Subgroup.isOpen_of_isClosed_of_finiteIndex _ c10)
    exact hx' hx
  have n01 : ¬ (stabilizerUpperTriangular r).FiniteIndex := fun hf => by
    obtain ⟨x, hx, hx'⟩ := h01 _ (Subgroup.isOpen_of_isClosed_of_finiteIndex _ c01)
    exact hx' hx
  fin_cases i
  · exact n10 hfi
  · exact n01 hfi
  · exact n10 hfi
  · exact n01 hfi

end Neumann

private theorem sym_four_diagonal (a b : k) :
    symmetricFourthPowerMatrix k !![a, 0; 0, b] = Matrix.diagonal ![a ^ 4, a ^ 3 * b, a ^ 2 * b ^ 2, a * b ^ 3, b ^ 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricFourthPowerMatrix]

private theorem diag_inj (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (hm : ∀ m : ℕ, 0 < m → a ^ m ≠ b ^ m) :
    Function.Injective ![a ^ 4, a ^ 3 * b, a ^ 2 * b ^ 2, a * b ^ 3, b ^ 4] := by
  have h1 := hm 1 (by norm_num)
  have h2 := hm 2 (by norm_num)
  have h3 := hm 3 (by norm_num)
  have h4 := hm 4 (by norm_num)
  have key : ∀ (x y : k), x ≠ 0 → ∀ m : ℕ, 0 < m → x * a ^ m ≠ x * b ^ m := fun x y hx m h e =>
    hm m h (mul_left_cancel₀ hx e)
  have n01 : a ^ 4 ≠ a ^ 3 * b := fun e => key (a ^ 3) 0 (pow_ne_zero _ ha) 1 (by norm_num) (by linear_combination e)
  have n02 : a ^ 4 ≠ a ^ 2 * b ^ 2 := fun e => key (a ^ 2) 0 (pow_ne_zero _ ha) 2 (by norm_num) (by linear_combination e)
  have n03 : a ^ 4 ≠ a * b ^ 3 := fun e => key a 0 ha 3 (by norm_num) (by linear_combination e)
  have n04 : a ^ 4 ≠ b ^ 4 := h4
  have n12 : a ^ 3 * b ≠ a ^ 2 * b ^ 2 := fun e => key (a ^ 2 * b) 0 (mul_ne_zero (pow_ne_zero _ ha) hb) 1 (by norm_num) (by linear_combination e)
  have n13 : a ^ 3 * b ≠ a * b ^ 3 := fun e => key (a * b) 0 (mul_ne_zero ha hb) 2 (by norm_num) (by linear_combination e)
  have n14 : a ^ 3 * b ≠ b ^ 4 := fun e => key b 0 hb 3 (by norm_num) (by linear_combination e)
  have n23 : a ^ 2 * b ^ 2 ≠ a * b ^ 3 := fun e => key (a * b ^ 2) 0 (mul_ne_zero ha (pow_ne_zero _ hb)) 1 (by norm_num) (by linear_combination e)
  have n24 : a ^ 2 * b ^ 2 ≠ b ^ 4 := fun e => key (b ^ 2) 0 (pow_ne_zero _ hb) 2 (by norm_num) (by linear_combination e)
  have n34 : a * b ^ 3 ≠ b ^ 4 := fun e => key (b ^ 3) 0 (pow_ne_zero _ hb) 1 (by norm_num) (by linear_combination e)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; simp at hij; first
        | exact n01 hij | exact n02 hij | exact n03 hij | exact n04 hij | exact n12 hij | exact n13 hij
        | exact n14 hij | exact n23 hij | exact n24 hij | exact n34 hij
        | exact n01 hij.symm | exact n02 hij.symm | exact n03 hij.symm | exact n04 hij.symm | exact n12 hij.symm
        | exact n13 hij.symm | exact n14 hij.symm | exact n23 hij.symm | exact n24 hij.symm | exact n34 hij.symm)

private theorem core [CharZero k] {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) k) (s g : Γ) (a b : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hm : ∀ m : ℕ, 0 < m → a ^ m ≠ b ^ m)
    (hs : (r s : Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, b])
    (hg : ∀ i j, (r g : Matrix (Fin 2) (Fin 2) k) i j ≠ 0) :
    IsIrr ((Units.map (symmetricFourthPowerMatrix k : Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 5) (Fin 5) k)).comp r) := by
  unfold IsIrr IsIrrSub
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hD : ∀ v ∈ W, (Matrix.diagonal ![a ^ 4, a ^ 3 * b, a ^ 2 * b ^ 2, a * b ^ 3, b ^ 4]).mulVec v ∈ W := by
    intro v hv
    have := hW s v hv
    simpa [hs, sym_four_diagonal] using this
  have hsingle := UpperTheory.V.Lib.Small.single_mem W _ (diag_inj a b ha hb hm) hD
  have hM : ∀ v ∈ W, (symmetricFourthPowerMatrix k (r g : Matrix (Fin 2) (Fin 2) k)).mulVec v ∈ W := fun v hv => by
    simpa using hW g v hv
  have g00 := hg 0 0
  have g01 := hg 0 1
  have g10 := hg 1 0
  have g11 := hg 1 1
  have hrow : ∀ j, symmetricFourthPowerMatrix k (r g : Matrix (Fin 2) (Fin 2) k) 0 j ≠ 0 := by
    intro j
    fin_cases j <;> simp [symmetricFourthPowerMatrix, g00, g01, g10, g11]
  have hcol : ∀ j, symmetricFourthPowerMatrix k (r g : Matrix (Fin 2) (Fin 2) k) j 0 ≠ 0 := by
    intro j
    fin_cases j <;> simp [symmetricFourthPowerMatrix, g00, g01, g10, g11]
  have hi1 : (Pi.single i 1 : Fin 5 → k) ∈ W := hsingle v hv i hi
  have h0 : (Pi.single 0 1 : Fin 5 → k) ∈ W :=
    hsingle _ (hM _ hi1) 0 (by simpa [Matrix.mulVec_single_one] using hrow i)
  have hall : ∀ j, (Pi.single j 1 : Fin 5 → k) ∈ W := fun j =>
    hsingle _ (hM _ h0) j (by simpa [Matrix.mulVec_single_one] using hcol j)
  rw [Submodule.eq_top_iff']
  intro x
  have e : x = ∑ i, x i • (Pi.single i 1 : Fin 5 → k) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (hall i)

end UpperTheory.V.Z.Sym.Ga.S4

namespace UpperTheory.V.Z.Sym.Ga.S4

private theorem irr_map_conj {k : Type} [Field k] {Γ : Type} [Group Γ] (r r' : Γ →* GL (Fin 2) k) (Q : GL (Fin 2) k)
    (h : ∀ x, r x = Q⁻¹ * r' x * Q)
    (hR : IsIrr ((Units.map (symmetricFourthPowerMatrix k : Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 5) (Fin 5) k)).comp r)) :
    IsIrr ((Units.map (symmetricFourthPowerMatrix k : Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 5) (Fin 5) k)).comp r') :=
  irr_conj _ _ (Units.map (symmetricFourthPowerMatrix k : Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 5) (Fin 5) k) Q⁻¹) (fun x => by
    simp only [MonoidHom.comp_apply]
    rw [h x, map_mul, map_mul, map_inv, inv_inv]) hR

private theorem sym_four_restrict_subgroup {k : Type} [Field k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) k) (H : Subgroup Γ) :
    (Ga.sym4 ρ).comp H.subtype =
      tw ((Units.map (symmetricFourthPowerMatrix k : Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 5) (Fin 5) k)).comp (ρ.comp H.subtype))
        (((Matrix.GeneralLinearGroup.det.comp ρ)⁻¹ ^ 2).comp H.subtype) :=
  MonoidHom.ext fun _ => rfl

end UpperTheory.V.Z.Sym.Ga.S4

theorem UpperTheory.V.Z.Sym.Ga.sym4Irr :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)), Continuous ρ → IrrOpen ρ → (∀ H : Subgroup Γ, IsOpen (H : Set Γ) → ∃ s ∈ H, ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l))) → IrrOpen (Ga.sym4 ρ) := by
  intro l _ Γ _ _ _ ρ hc hI hs H hH
  obtain ⟨s, hsH, a, b, hab, hch⟩ := hs H hH
  have hm : ∀ m : ℕ, 0 < m → (a : Qbar l) ^ m ≠ (b : Qbar l) ^ m := by
    intro m hm e
    apply hab
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
    rw [div_pow, div_eq_one]
    exact Units.ext (by simpa using e)
  have hne : (a : Qbar l) ≠ b := by simpa using hm 1 one_pos
  obtain ⟨Q, hQ⟩ := S4.eig_basis _ _ _ hne hch
  let c : GL (Fin 2) (Qbar l) →* GL (Fin 2) (Qbar l) := (MulAut.conj Q⁻¹).toMonoidHom
  have hcx : ∀ x, c x = Q⁻¹ * x * Q := fun x => by simp [c, MulAut.conj_apply]
  let r : H →* GL (Fin 2) (Qbar l) := c.comp (ρ.comp H.subtype)
  have hrx : ∀ x : H, r x = Q⁻¹ * ρ x * Q := fun x => hcx _
  have hrs : (r ⟨s, hsH⟩ : Matrix (Fin 2) (Fin 2) (Qbar l)) = !![(a : Qbar l), 0; 0, (b : Qbar l)] := by
    rw [hrx, Units.val_mul, Units.val_mul, mul_assoc]
    show _ * ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) * _) = _
    rw [hQ, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hcont : ∀ i j, Continuous fun x : H => (r x : Matrix (Fin 2) (Fin 2) (Qbar l)) i j := by
    intro i j
    have h1 : Continuous fun x : H => ((ρ x : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
      Units.continuous_val.comp (hc.comp continuous_subtype_val)
    have h2 : Continuous fun x : H => ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) *
        (ρ x : Matrix (Fin 2) (Fin 2) (Qbar l)) * (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
      (continuous_const.matrix_mul h1).matrix_mul continuous_const
    have h3 := h2.matrix_elem i j
    refine h3.congr fun x => ?_
    rw [hrx, Units.val_mul, Units.val_mul]
  have hirr : ∀ K : Subgroup H, IsOpen (K : Set H) → IsIrr (c.comp (ρ.comp (K.map H.subtype).subtype)) := by
    intro K hK
    have hK' : IsOpen ((K.map H.subtype : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.coe_map]
      exact hH.isOpenMap_subtype_val _ hK
    exact S4.irr_conj _ (ρ.comp (K.map H.subtype).subtype) Q (fun x => by
      show ρ x = Q * c (ρ x) * Q⁻¹
      rw [hcx]; group) (hI _ hK')
  have h10 : ∀ K : Subgroup H, IsOpen (K : Set H) → ∃ x ∈ K, (r x : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    intro K hK
    obtain ⟨⟨x, hx⟩, hx'⟩ := S4.exists_nonzero_lower_entry_of_irreducible _ (hirr K hK)
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨y, hy, hx'⟩
  have h01 : ∀ K : Subgroup H, IsOpen (K : Set H) → ∃ x ∈ K, (r x : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 1 ≠ 0 := by
    intro K hK
    obtain ⟨⟨x, hx⟩, hx'⟩ := S4.exists_nonzero_upper_entry_of_irreducible _ (hirr K hK)
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨y, hy, hx'⟩
  obtain ⟨g, hg⟩ := S4.exists_full r hcont h10 h01
  have hR := S4.core r ⟨s, hsH⟩ g a b a.ne_zero b.ne_zero hm hrs hg
  have hR2 := S4.irr_map_conj r (ρ.comp H.subtype) Q hrx hR
  rw [S4.sym_four_restrict_subgroup]
  exact (UpperTheory.V.Sd.shapeFacts l H 5 _ _).2.2.2.2.2 hR2
