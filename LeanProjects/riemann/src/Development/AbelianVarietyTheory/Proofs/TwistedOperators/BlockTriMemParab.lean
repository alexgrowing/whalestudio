import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim.Coset

def Pres (r t : ℕ) (v : Equiv.Perm (Fin (r + t))) : Prop :=
  ∀ (i : Fin t) (j : Fin r), Fin.natAdd r i ≠ v (Fin.castAdd t j)

theorem perm_normal (r t : ℕ) (w₀ : Equiv.Perm (Fin (r + t))) :
    ∃ (v w u : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)),
      Nice r t w S ∧ Pres r t v ∧ Pres r t u ∧ w₀ = v * w * u := by
  classical

  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin r),
      A = Finset.univ.filter (fun s => ¬ ((w₀ (Fin.castAdd t s) : ℕ) < r)) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin t),
      C = Finset.univ.filter (fun x => (w₀ (Fin.natAdd r x) : ℕ) < r) := ⟨_, rfl⟩
  have hmemA : ∀ s, s ∈ A ↔ ¬ ((w₀ (Fin.castAdd t s) : ℕ) < r) := fun s => by simp [hA]
  have hmemC : ∀ x, x ∈ C ↔ (w₀ (Fin.natAdd r x) : ℕ) < r := fun x => by simp [hC]
  have hsum : ∑ p : Fin (r + t), (if ((w₀ p : Fin (r + t)) : ℕ) < r then 1 else 0) = r := by
    refine (Equiv.sum_comp w₀ (fun q : Fin (r + t) => if (q : ℕ) < r then 1 else 0)).trans ?_
    rw [Fin.sum_univ_add]
    simp
  rw [Fin.sum_univ_add] at hsum
  simp only [Finset.sum_boole, Nat.cast_id] at hsum
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r))) (fun s => (w₀ (Fin.castAdd t s) : ℕ) < r)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  have hcard : A.card = C.card := by
    rw [hA, hC]
    omega
  obtain ⟨e⟩ : Nonempty (A ≃ C) := Fintype.card_eq.mp (by simpa using hcard)

  let φ : Fin r ⊕ Fin t → Fin r ⊕ Fin t :=
    Sum.elim (fun s => if h : s ∈ A then Sum.inr (e ⟨s, h⟩).1 else Sum.inl s)
      (fun x => if h : x ∈ C then Sum.inl (e.symm ⟨x, h⟩).1 else Sum.inr x)
  have hφ : Function.Involutive φ := by
    rintro (s | x)
    · by_cases h : s ∈ A
      · simp [φ, h, (e ⟨s, h⟩).2]
      · simp [φ, h]
    · by_cases h : x ∈ C
      · simp [φ, h, (e.symm ⟨x, h⟩).2]
      · simp [φ, h]
  let w : Equiv.Perm (Fin (r + t)) := finSumFinEquiv.permCongr (Function.Involutive.toPerm φ hφ)
  have hw : ∀ z, w (finSumFinEquiv z) = finSumFinEquiv (φ z) := fun z => by
    simp [w, Equiv.permCongr_apply]
  have hww : ∀ x, w (w x) = x := fun x => by
    obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective x
    rw [hw, hw, hφ]
  have hwA : ∀ s, s ∈ A → ∃ x ∈ C, w (Fin.castAdd t s) = Fin.natAdd r x := fun s h =>
    ⟨_, (e ⟨s, h⟩).2, by rw [← finSumFinEquiv_apply_left, hw]; simp [φ, h]⟩
  have hwA' : ∀ s, s ∉ A → w (Fin.castAdd t s) = Fin.castAdd t s := fun s h => by
    rw [← finSumFinEquiv_apply_left, hw]; simp [φ, h]
  refine ⟨w₀ * w, w, 1, A, ?_, ?_, ?_, ?_⟩
  · unfold GlobalTheory.TypeDim.Nice
    refine ⟨fun i hi => hwA' i hi, fun i hi => ?_, fun h0 => ?_⟩
    · obtain ⟨x, -, hx⟩ := hwA i hi
      have hsymm : w.symm (Fin.castAdd t i) = w (Fin.castAdd t i) :=
        (Equiv.symm_apply_eq w).mpr (hww _).symm
      rw [hsymm, hx]
      simp
    · have hC0 : C = ∅ := Finset.card_eq_zero.mp (by rw [← hcard, h0, Finset.card_empty])
      refine Equiv.ext fun x => ?_
      obtain ⟨z, rfl⟩ := finSumFinEquiv.surjective x
      rw [hw]
      rcases z with s | y <;> simp [φ, h0, hC0]
  · intro i j hij
    have hlt : ((w₀ (w (Fin.castAdd t j)) : Fin (r + t)) : ℕ) < r := by
      by_cases hj : j ∈ A
      · obtain ⟨x, hx, hxw⟩ := hwA j hj
        rw [hxw]
        exact (hmemC x).mp hx
      · rw [hwA' j hj]
        simpa [hmemA] using hj
    rw [Equiv.Perm.mul_apply] at hij
    rw [← hij] at hlt
    simp at hlt
  · intro i j hij
    have h1 := congrArg Fin.val hij
    have h2 := j.2
    simp only [Equiv.Perm.one_apply, Fin.coe_natAdd, Fin.coe_castAdd] at h1
    omega
  · have hww' : w * w = 1 := Equiv.ext fun x => hww x
    rw [mul_one, mul_assoc, hww', mul_one]

private theorem blockIndex_true_eq_natAdd (r t : ℕ) (i : Fin t) :
    part r t ⟨true, i⟩ = Fin.natAdd r i := Fin.ext (by simp [part])

private theorem blockIndex_false_eq_castAdd (r t : ℕ) (i : Fin r) :
    part r t ⟨false, i⟩ = Fin.castAdd t i := Fin.ext (by simp [part])

private theorem mem_parab_iff_lower_left_eq_zero {R : Type} [CommRing R] {r t : ℕ} {g : GL (Fin (r + t)) R} :
    g ∈ parab R (part r t) ↔ ∀ (i : Fin t) (j : Fin r), g.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  rw [mem_parab_iff]
  constructor
  · intro h i j
    have := h true false i j (by decide)
    rwa [blockIndex_true_eq_natAdd, blockIndex_false_eq_castAdd] at this
  · intro h a b i j hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · rw [blockIndex_true_eq_natAdd, blockIndex_false_eq_castAdd]
      exact h i j
    · exact absurd hab (by decide)

theorem permGL_mem_parab (F : Type) [Field F] {r t : ℕ} {v : Equiv.Perm (Fin (r + t))} (hv : Pres r t v) :
    Parabolic.permGL F v ∈ parab F (part r t) := by
  rw [mem_parab_iff_lower_left_eq_zero]
  intro i j
  rw [GlobalTheory.Parabolic.permGL_apply, if_neg (hv i j)]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝒪[k]) (B : GL (Fin n) 𝓀[k])
    (h : ∀ i j, IsLocalRing.residue 𝒪[k] (M i j) = B.val i j) : ∃ u : GL (Fin n) 𝒪[k], u.val = M := by
  have hM : (IsLocalRing.residue 𝒪[k]).mapMatrix M = B.val := Matrix.ext fun i j => h i j

  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hM]
    exact (Matrix.isUnits_det_units B).ne_zero
  exact ⟨(M.isUnit_iff_isUnit_det.mpr hdet).unit, rfl⟩

theorem exists_lift {n : ℕ} (B : GL (Fin n) 𝓀[k]) :
    ∃ u : GL (Fin n) 𝒪[k], red k n u = B ∧ ∀ i j, B.val i j = 0 → u.val i j = 0 := by
  classical

  obtain ⟨u, hu⟩ := GlobalTheory.TypeDim.Coset.exists_unit (k := k)
    (fun i j => if B.val i j = 0 then 0 else Function.surjInv IsLocalRing.residue_surjective (B.val i j)) B
    (fun i j => by
      by_cases h : B.val i j = 0
      · simp [h]
      · simp [h, Function.surjInv_eq])
  refine ⟨u, Matrix.GeneralLinearGroup.ext fun i j => ?_, fun i j h => by rw [hu]; simp [h]⟩
  rw [red_val, hu]
  by_cases h : B.val i j = 0
  · simp [h]
  · simp [h, Function.surjInv_eq]

variable (k) in

def permO (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) 𝒪[k] := (Matrix.permMatrixHom (R := 𝒪[k])).toHomUnits

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem permO_apply {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permO k n w).val i j = if i = w j then 1 else 0 := by
  simp [permO, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.symm_apply_eq]

theorem incl_permO {n : ℕ} (w : Equiv.Perm (Fin n)) : incl k n (permO k n w) = Parabolic.permGL k w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [incl_val, permO_apply, GlobalTheory.Parabolic.permGL_apply]
  split_ifs <;> simp

theorem red_permO {n : ℕ} (w : Equiv.Perm (Fin n)) : red k n (permO k n w) = Parabolic.permGL 𝓀[k] w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [red_val, permO_apply, GlobalTheory.Parabolic.permGL_apply]
  split_ifs <;> simp

theorem exists_blocks {r t : ℕ} (y : GL (Fin (r + t)) 𝒪[k]) (hy : red k (r + t) y ∈ parab 𝓀[k] (part r t)) :
    ∃ a d, HasBlocks y a d := by

  obtain ⟨a, ha⟩ := GlobalTheory.TypeDim.Coset.exists_unit (k := k)
    (fun i j => y.val (Fin.castAdd t i) (Fin.castAdd t j))
    (GlobalTheory.SmGL.leviProj 𝓀[k] (part r t) ⟨_, hy⟩ false) (fun i j => by
      rw [GlobalTheory.SmGL.leviProj_apply, blockIndex_false_eq_castAdd, blockIndex_false_eq_castAdd]
      simp only [Subgroup.coe_mk]
      rw [red_val])
  obtain ⟨d, hd⟩ := GlobalTheory.TypeDim.Coset.exists_unit (k := k)
    (fun i j => y.val (Fin.natAdd r i) (Fin.natAdd r j))
    (GlobalTheory.SmGL.leviProj 𝓀[k] (part r t) ⟨_, hy⟩ true) (fun i j => by
      rw [GlobalTheory.SmGL.leviProj_apply, blockIndex_true_eq_natAdd, blockIndex_true_eq_natAdd]
      simp only [Subgroup.coe_mk]
      rw [red_val])
  refine ⟨a, d, ?_⟩
  unfold HasBlocks
  refine ⟨fun i j => by rw [ha], fun i j => by rw [hd], fun i j => ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, ← red_val]
  exact mem_parab_iff_lower_left_eq_zero.mp hy i j

theorem hasBlocks_split {r t : ℕ} {y : GL (Fin (r + t)) 𝒪[k]} {a : GL (Fin r) 𝒪[k]} {d : GL (Fin t) 𝒪[k]}
    (h : HasBlocks y a d) : HasBlocks (diagO a⁻¹ 1 * y) 1 d := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold HasBlocks
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [diagO_ul, diagO_ur, h1, zero_mul, Finset.sum_const_zero, add_zero]
    rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel]
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [diagO_ll, diagO_lr, h2, zero_mul, Finset.sum_const_zero, zero_add]
    rw [← Matrix.mul_apply, Units.val_one, Matrix.one_mul]
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [diagO_ll, diagO_lr, zero_mul, Finset.sum_const_zero, zero_add, Units.val_one,
      Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact h3 i j

theorem blockTri_mem_parab {F : Type} [Field F] {r t : ℕ} {g : GL (Fin (r + t)) F}
    (hg : g ∈ Formalism.L2.DIV.blockTri (κ := F) (fun i : Fin (r + t) => if (i : ℕ) < r then 0 else 1)) :
    g ∈ parab F (part r t) := by
  rw [mem_parab_iff_lower_left_eq_zero]
  intro i j
  refine Formalism.L2.DIV.mem_blockTri.mp hg _ _ ?_
  have hj := j.2
  simp [hj]

theorem coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (g : GL (Fin (r + t)) k), ∃ (p : parab k (part r t)) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) (a a₁ : GL (Fin r) 𝒪[k]) (h : GL (Fin (r + t)) 𝒪[k]) (d : GL (Fin t) 𝒪[k]), Nice r t w S ∧ red k r a₁ = 1 ∧ HasBlocks h a₁ d ∧ g = p * (GlobalTheory.Parabolic.permGL k w * diagOne k r t a * incl k (r + t) h) := by
  intro k _ _ _ _ r t g
  classical

  obtain ⟨b, hb, w', hw', hg⟩ := GlobalTheory.SplitWeil.iwasawa_blockTriangular k (Fin (r + t))
    (fun i : Fin (r + t) => if (i : ℕ) < r then 0 else 1) g
  obtain ⟨κ, hκ⟩ := hw'
  have hκ' : incl k (r + t) κ = w' := hκ
  have hbP : b ∈ parab k (part r t) :=
    blockTri_mem_parab (Formalism.L2.DIV.mem_blockTri.mpr fun i j hij => hb hij)

  have hmono : Monotone (fun i : Fin (r + t) => if (i : ℕ) < r then 0 else 1) := by
    intro x y hxy
    have : (x : ℕ) ≤ y := hxy
    dsimp only
    split_ifs <;> omega
  obtain ⟨w₀, p', p, hbr⟩ := GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri 𝓀[k] (r + t) _ _ hmono hmono
    (red k (r + t) κ)
  obtain ⟨v, w, u, S, hN, hv, hu, hw₀⟩ := perm_normal r t w₀
  have hq' : (p' : GL (Fin (r + t)) 𝓀[k]) * GlobalTheory.Parabolic.permGL 𝓀[k] v ∈ parab 𝓀[k] (part r t) :=
    mul_mem (blockTri_mem_parab p'.2) (permGL_mem_parab _ hv)
  have hq : GlobalTheory.Parabolic.permGL 𝓀[k] u * (p : GL (Fin (r + t)) 𝓀[k]) ∈ parab 𝓀[k] (part r t) :=
    mul_mem (permGL_mem_parab _ hu) (blockTri_mem_parab p.2)
  obtain ⟨Q', hQ'red, hQ'0⟩ := exists_lift (k := k)
    ((p' : GL (Fin (r + t)) 𝓀[k]) * GlobalTheory.Parabolic.permGL 𝓀[k] v)
  obtain ⟨Q, hQred, -⟩ := exists_lift (k := k)
    (GlobalTheory.Parabolic.permGL 𝓀[k] u * (p : GL (Fin (r + t)) 𝓀[k]))
  have hredκ : red k (r + t) κ =
      red k (r + t) Q' * red k (r + t) (permO k (r + t) w) * red k (r + t) Q := by
    rw [hQ'red, hQred, red_permO, hbr, hw₀, map_mul, map_mul]
    simp only [mul_assoc]
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁, κ₁ = (Q' * permO k (r + t) w * Q)⁻¹ * κ := ⟨_, rfl⟩
  have hκ₁red : red k (r + t) κ₁ = 1 := by
    rw [hκ₁]
    simp only [map_mul, map_inv]
    rw [← hredκ, inv_mul_cancel]
  obtain ⟨y, hy⟩ : ∃ y, y = Q * κ₁ := ⟨_, rfl⟩
  have hyP : red k (r + t) y ∈ parab 𝓀[k] (part r t) := by
    rw [hy, map_mul, hκ₁red, mul_one, hQred]
    exact hq
  obtain ⟨a, d, had⟩ := exists_blocks y hyP
  have hInclQ' : incl k (r + t) Q' ∈ parab k (part r t) := by
    rw [mem_parab_iff_lower_left_eq_zero]
    intro i j
    rw [incl_val, hQ'0 _ _ (mem_parab_iff_lower_left_eq_zero.mp hq' i j)]
    simp
  have hdiag : diagO a 1 * diagO a⁻¹ 1 = (1 : GL (Fin (r + t)) 𝒪[k]) := by
    unfold diagO
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one]
  obtain ⟨h, hh⟩ : ∃ h, h = diagO a⁻¹ 1 * y := ⟨_, rfl⟩
  have hhb : HasBlocks h 1 d := by
    rw [hh]
    exact hasBlocks_split had
  refine ⟨⟨b * incl k (r + t) Q', mul_mem hbP hInclQ'⟩, w, S, a, 1, h, d, hN, map_one _, hhb, ?_⟩
  have hcancel : diagO a 1 * (diagO a⁻¹ 1 * y) = y := by rw [← mul_assoc, hdiag, one_mul]
  have hκeq : κ = Q' * permO k (r + t) w * (diagO a 1 * h) := by
    rw [hh, hcancel, hy, hκ₁]
    group
  rw [hg, ← hκ', hκeq, map_mul, map_mul, map_mul, incl_permO, incl_diagO_one]
  simp only [Subgroup.coe_mk, mul_assoc]

end GlobalTheory.TypeDim.Coset
