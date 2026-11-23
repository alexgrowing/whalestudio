import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituentStatement

noncomputable section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
namespace GlobalTheory.GLp.ParLabel

section Abstract
variable {G : Type} [Group G] [Fintype G]

theorem eq_sum_single (e : MonoidAlgebra ℂ G) : e = ∑ x, MonoidAlgebra.single x (e.coeff x) := by
  ext y
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem idem_eq_zero (D : MonoidAlgebra ℂ G) (h : D * D = D) (h0 : D.coeff 1 = 0) : D = 0 := by
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ D) := by
    refine LinearMap.ext fun y => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ D) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    change (D * MonoidAlgebra.basis G ℂ x).coeff x = 0
    simp [h0]
  have := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hi).1 ht
  simpa using congrArg (fun φ => φ 1) this

def mean (U : Subgroup G) : MonoidAlgebra ℂ G := ∑ u : U, MonoidAlgebra.single (u : G) (Fintype.card U : ℂ)⁻¹

theorem mean_idem (U : Subgroup G) : mean U * mean U = mean U := by
  have h1 : ∀ (u : U) (c : ℂ), MonoidAlgebra.single (u : G) c * mean U = c • mean U := by
    intro u c
    simp only [mean, Finset.mul_sum, Finset.smul_sum, MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single,
      smul_eq_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun x => by simp)
  nth_rewrite 1 [mean]
  rw [Finset.sum_mul]
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by simp), one_smul]

theorem mean_comm (U : Subgroup G) (x : G) (hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (c : ℂ) :
    Commute (MonoidAlgebra.single x c) (mean U) := by
  let φ : U → U := fun u => ⟨x * u * x⁻¹, hx u u.2⟩
  have hφ : Function.Bijective φ := Finite.injective_iff_bijective.1 (fun u v h => by
    have := congrArg Subtype.val h
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this)
  unfold Commute SemiconjBy
  simp only [mean, Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single]
  exact Fintype.sum_bijective φ hφ _ _ (fun u => by simp [φ, mul_comm])

variable {A : Type} [Group A] [Fintype A]

def push (i : A →* G) (e : MonoidAlgebra ℂ A) : MonoidAlgebra ℂ G := ∑ x, MonoidAlgebra.single (i x) (e.coeff x)

theorem push_mul (i : A →* G) (e e' : MonoidAlgebra ℂ A) : push i (e * e') = push i e * push i e' := by
  have h : ∀ e, push i e = MonoidAlgebra.mapDomainAlgHom ℂ ℂ i e := by
    intro e
    conv_rhs => rw [eq_sum_single e]
    simp [push, map_sum]
  simp only [h, map_mul]

theorem tr_sum {ι : Type} (s : Finset ι) (e : ι → MonoidAlgebra ℂ G) (χ : G → ℂ) :
    tr (∑ i ∈ s, e i) χ = ∑ i ∈ s, tr (e i) χ := by
  simp only [tr, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem tr_single (x : G) (c : ℂ) (χ : G → ℂ) : tr (MonoidAlgebra.single x c) χ = c * χ x := by
  simp [tr, Finsupp.single_apply]

theorem coeff_zOf (χ : G → ℂ) (x : G) : (zOf χ).coeff x = χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ := by
  simp [zOf, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

variable {B : Type} [Group B] [Fintype B]

theorem key (i : A →* G) (j : B →* G) (hc : ∀ x y, Commute (i x) (j y)) (U : Subgroup G)
    (hi : ∀ x, ∀ u ∈ U, i x * u * (i x)⁻¹ ∈ U) (hj : ∀ x, ∀ u ∈ U, j x * u * (j x)⁻¹ ∈ U)
    (α : A → ℂ) (β : B → ℂ) (ψ : G → ℂ) (hα : IsIrr α) (hβ : IsIrr β) (hψ : IsIrr ψ)
    (hne : zOf ψ * (push i (zOf α) * (push j (zOf β) * mean U)) ≠ 0) :
    ∑ p : A × B, (∑ u : U, ψ (i p.1 * j p.2 * u)) * (α p.1⁻¹ * β p.2⁻¹) ≠ 0 := by
  intro h0
  apply hne
  have c1 : Commute (push i (zOf α)) (mean U) := Commute.sum_left _ _ _ fun x _ => mean_comm U _ (hi x) _
  have c2 : Commute (push j (zOf β)) (mean U) := Commute.sum_left _ _ _ fun x _ => mean_comm U _ (hj x) _
  have c3 : Commute (push i (zOf α)) (push j (zOf β)) :=
    Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => by
      unfold Commute SemiconjBy
      simp only [MonoidAlgebra.single_mul_single]
      rw [(hc x y).eq, mul_comm]
  have i1 : IsIdempotentElem (push i (zOf α)) := by
    unfold IsIdempotentElem
    rw [← push_mul, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central A α α hα hα).1, if_pos rfl]
  have i2 : IsIdempotentElem (push j (zOf β)) := by
    unfold IsIdempotentElem
    rw [← push_mul, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central B β β hβ hβ).1, if_pos rfl]
  have i3 : IsIdempotentElem (zOf ψ) := by
    unfold IsIdempotentElem
    rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G ψ ψ hψ hψ).1, if_pos rfl]
  have hz := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G ψ ψ hψ hψ).2.1
  have i4 : IsIdempotentElem (zOf ψ * (push i (zOf α) * (push j (zOf β) * mean U))) :=
    IsIdempotentElem.mul_of_commute (hz _) i3
      (IsIdempotentElem.mul_of_commute (c3.mul_right c1) i1 (IsIdempotentElem.mul_of_commute c2 i2 (mean_idem U)))
  apply idem_eq_zero _ i4
  rw [hz, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G _ ψ).2.2]
  have : tr (push i (zOf α) * (push j (zOf β) * mean U)) ψ =
      (α 1 / (Fintype.card A : ℂ) * (β 1 / (Fintype.card B : ℂ)) * (Fintype.card U : ℂ)⁻¹) *
        ∑ p : A × B, (∑ u : U, ψ (i p.1 * j p.2 * u)) * (α p.1⁻¹ * β p.2⁻¹) := by
    rw [Fintype.sum_prod_type, push, Finset.sum_mul, tr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [push, Finset.sum_mul, Finset.mul_sum, tr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mean, Finset.mul_sum, Finset.mul_sum, tr_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [MonoidAlgebra.single_mul_single, tr_single, coeff_zOf, mul_assoc]
    ring
  rw [this, h0, mul_zero, mul_zero]

end Abstract

section Blocks
variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def sp (M : Mt g (a + b)) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod g) := M.submatrix finSumFinEquiv finSumFinEquiv

theorem sp_mul (M N : Mt g (a + b)) : sp (M * N) = sp M * sp N := by
  simp [sp, Matrix.submatrix_mul_equiv]

theorem sp_one : sp (1 : Mt g (a + b)) = 1 := by simp [sp]

theorem sp_inj {M N : Mt g (a + b)} (h : sp M = sp N) : M = N := by
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [sp] using this

theorem tl_eq (M : Mt g (a + b)) : tl a M = (sp M).toBlocks₁₁ := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [tl, entN, sp, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_eq (M : Mt g (a + b)) : br a b M = (sp M).toBlocks₂₂ := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [br, entN, sp, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem inPar_iff (M : Mt g (a + b)) : InPar a M ↔ (sp M).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have hi' := i.2
    have := congrFun (congrFun h ⟨i - a, by omega⟩) ⟨j, hj⟩
    simp only [sp, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply] at this
    convert this using 2 <;> ext <;> simp <;> omega

theorem sp_blk (x : Gn g a) (y : Gn g b) :
    sp (blk a b (a + b) x y : Mt g (a + b)) = Matrix.fromBlocks (x : Mt g a) 0 0 (y : Mt g b) := by
  set M : Mt g (a + b) := fun i j : Fin (a + b) =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN (y : Mt g b) (i - a) (j - a) else 0 with hM
  have h1 : sp M = Matrix.fromBlocks (x : Mt g a) 0 0 (y : Mt g b) := by
    ext (i | i) (j | j) <;> have hi := i.2 <;> have hj := j.2 <;> change M _ _ = _ <;> simp [hM, entN, hi, hj]
  have h2 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    change IsUnit (sp M).det
    rw [h1, Matrix.det_fromBlocks_zero₂₁]
    exact (Matrix.isUnits_det_units x).mul (Matrix.isUnits_det_units y)
  rw [← h1]
  change sp (toG M : Mt g (a + b)) = _
  rw [toG, dif_pos h2]
  rfl

theorem blk_mul (x x' : Gn g a) (y y' : Gn g b) :
    blk a b (a + b) (x * x') (y * y') = blk a b (a + b) x y * blk a b (a + b) x' y' := by
  apply Units.ext
  apply sp_inj
  rw [Units.val_mul, sp_mul, sp_blk, sp_blk, sp_blk]
  simp [Matrix.fromBlocks_multiply]

theorem blk_one : blk a b (a + b) (1 : Gn g a) 1 = 1 := by
  apply Units.ext
  apply sp_inj
  rw [sp_blk, Units.val_one, Units.val_one, Units.val_one, sp_one, Matrix.fromBlocks_one]

def Over (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) : Prop :=
  InPar a (p : Mt g (a + b)) ∧ tl a (p : Mt g (a + b)) = (x : Mt g a) ∧ br a b (p : Mt g (a + b)) = (y : Mt g b)

theorem over_iff (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) :
    Over p x y ↔ ∃ Z, sp (p : Mt g (a + b)) = Matrix.fromBlocks (x : Mt g a) Z 0 (y : Mt g b) := by
  rw [Over, inPar_iff, tl_eq, br_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, by rw [← h1, ← h2, ← h3, Matrix.fromBlocks_toBlocks]⟩
  · rintro ⟨Z, h⟩
    rw [h]
    simp

theorem Over.mul {p q : Gn g (a + b)} {x x' : Gn g a} {y y' : Gn g b} (h : Over p x y) (h' : Over q x' y') :
    Over (p * q) (x * x') (y * y') := by
  rw [over_iff] at *
  obtain ⟨Z, h⟩ := h
  obtain ⟨Z', h'⟩ := h'
  refine ⟨(x : Mt g a) * Z' + Z * (y' : Mt g b), ?_⟩
  rw [Units.val_mul, sp_mul, h, h']
  simp [Matrix.fromBlocks_multiply]

theorem over_blk (x : Gn g a) (y : Gn g b) : Over (blk a b (a + b) x y) x y := (over_iff _ _ _).2 ⟨0, sp_blk x y⟩

def rad (g a b : ℕ) [Fact g.Prime] : Subgroup (Gn g (a + b)) where
  carrier := {u | Over u (1 : Gn g a) (1 : Gn g b)}
  one_mem' := by simpa [blk_one] using over_blk (1 : Gn g a) (1 : Gn g b)
  mul_mem' := fun h h' => by simpa using Over.mul h h'
  inv_mem' := fun {u} h => by
    have hp : ∀ k : ℕ, Over (u ^ k) (1 : Gn g a) (1 : Gn g b) := by
      intro k
      induction k with
      | zero => simpa [blk_one] using over_blk (1 : Gn g a) (1 : Gn g b)
      | succ k ih => simpa [pow_succ] using Over.mul ih h
    have : u⁻¹ = u ^ (orderOf u - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
    rw [Set.mem_setOf_eq, this]
    exact hp _

def levi (g a b : ℕ) [Fact g.Prime] : Gn g a × Gn g b →* Gn g (a + b) where
  toFun p := blk a b (a + b) p.1 p.2
  map_one' := blk_one
  map_mul' p q := blk_mul _ _ _ _

theorem res_eq (ψ : Gn g (a + b) → ℂ) (x : Gn g a) (y : Gn g b) :
    res a b ψ x y = ((g : ℂ) ^ (a * b))⁻¹ * ∑ u : rad g a b, ψ (levi g a b (x, y) * u) := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => levi g a b (x, y) * u) ?_ ?_ ?_ ?_
  · intro u _
    have := (over_blk x y).mul u.2
    simp only [mul_one] at this
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
  · intro u _ v _ h
    exact Subtype.ext (mul_left_cancel h)
  · intro p hp
    have h : Over p x y := (Finset.mem_filter.1 hp).2
    have := (over_blk x⁻¹ y⁻¹).mul h
    simp only [inv_mul_cancel] at this
    refine ⟨⟨_, this⟩, Finset.mem_univ _, ?_⟩
    change levi g a b (x, y) * (levi g a b (x, y)⁻¹ * p) = p
    rw [map_inv, mul_inv_cancel_left]
  · intro u _
    rfl

end Blocks

section Main
variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)

theorem actK_single (x : Gn g n) (c : ℂ) : actK π (MonoidAlgebra.single x c) = c • π (lift g n x) := by
  simp [actK, Finsupp.single_apply]

end Main

end GlobalTheory.GLp.ParLabel
