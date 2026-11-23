import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideSide

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ContractingCosets

open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal

theorem isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (A : G) :
    IsOpen {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} := by
  have h : {g | ∃ x ∈ K, ∃ y ∈ K, g = x * A * y} =
      ⋃ x ∈ K, (fun y => x * A * y) '' (K : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    exact ⟨fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩,
      fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, hy, e.symm⟩⟩
  rw [h]
  exact isOpen_biUnion fun x _ => (Homeomorph.mulLeft (x * A)).isOpenMap _ hK

theorem eq_central_mul {G : Type*} [Group G] {x y x' y' A B : G}
    (hz : (x * A * y)⁻¹ * (x' * B * y') ∈ Subgroup.center G) :
    B = ((x * A * y)⁻¹ * (x' * B * y')) * ((x'⁻¹ * x) * A * (y * y'⁻¹)) := by
  have h := Subgroup.mem_center_iff.1 hz (x'⁻¹ * x * A * y)
  calc B = (x'⁻¹ * x * A * y) * ((x * A * y)⁻¹ * (x' * B * y')) * y'⁻¹ := by group
    _ = ((x * A * y)⁻¹ * (x' * B * y')) * (x'⁻¹ * x * A * y) * y'⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k]

theorem entry_bound {N : ℕ} {P Q B : Matrix (Fin N) (Fin N) k} {C : ValueGroupWithZero k}
    (hP : ∀ i j, valuation k (P i j) ≤ 1) (hQ : ∀ i j, valuation k (Q i j) ≤ 1)
    (hB : ∀ i j, valuation k (B i j) ≤ C) (i j : Fin N) :
    valuation k ((P * B * Q) i j) ≤ C :=
  _root_.UpperTheory.Reformulated.B.Ylb4.main hP hQ hB i j

theorem coe_pow_of_diag {N : ℕ} {δ : Fin N → k} {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    ((a ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => δ i ^ r := by
  rw [Units.val_pow_eq_pow_val, ha, diagonal_pow]
  rfl

theorem coe_inv_pow_of_diag {N : ℕ} {δ : Fin N → k} (hδ : ∀ i, δ i ≠ 0) {a : GL (Fin N) k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ) (r : ℕ) :
    (((a ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = diagonal fun i => (δ i)⁻¹ ^ r := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [coe_pow_of_diag ha, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_pow, mul_inv_cancel₀ (hδ i), one_pow]

theorem val_le_one_of_mem {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : GL (Fin N) k} (hg : g ∈ integralGL k N) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (((mem_integralGL_iff k N).1 hg).1 i j)

theorem le_of_eq_central_mul {N : ℕ} [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : Fin N → k} (t : kˣ) (ht : valuation k (t : k) < 1)
    (hδ : ∀ i, δ i = t ∨ δ i = 1) {i₁ i₂ : Fin N} (h₁ : δ i₁ = t) (h₂ : δ i₂ = 1)
    {a : GL (Fin N) k} (ha : (a : Matrix (Fin N) (Fin N) k) = diagonal δ)
    {p q z : GL (Fin N) k} (hp : p ∈ integralGL k N) (hq : q ∈ integralGL k N)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) {r r' : ℕ}
    (h : a ^ r = z * (p * a ^ r' * q)) : r ≤ r' := by
  have hδ0 : ∀ i, δ i ≠ 0 := fun i => by
    rcases hδ i with h | h <;> rw [h]
    · exact t.ne_zero
    · exact one_ne_zero
  have hvt0 : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  have hvt1 : 1 ≤ (valuation k (t : k))⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht |>.le
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  obtain ⟨c', hc'⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1
    (inv_mem hz)
  have hcc : c * c' = 1 := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂)
      (mul_inv_cancel z)
    simp only [Units.val_mul, ← hc, ← hc', Units.val_one] at e
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using e

  have hB : ∀ i j, valuation k (((a ^ r' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
    intro i j
    rw [coe_pow_of_diag ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow]
      refine pow_le_one₀ zero_le' ?_
      rcases hδ i with h | h <;> rw [h]
      · exact ht.le
      · simp
    · rw [diagonal_apply_ne _ hij]; simp

  have hB' : ∀ i j, valuation k ((((a ^ r')⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤
      (valuation k (t : k))⁻¹ ^ r' := by
    intro i j
    rw [coe_inv_pow_of_diag hδ0 ha]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, map_pow, map_inv₀]
      rcases hδ i with h | h <;> rw [h]
      simpa using one_le_pow₀ hvt1
    · rw [diagonal_apply_ne _ hij]; simp

  have hc1 : 1 ≤ valuation k c := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₂ i₂) h
    simp only [Units.val_mul (a := z), ← hc] at e
    rw [coe_pow_of_diag ha, diagonal_apply_eq, h₂, one_pow, Matrix.scalar_apply,
      Matrix.diagonal_mul] at e
    have b := entry_bound (val_le_one_of_mem hp) (val_le_one_of_mem hq) hB i₂ i₂
    have e' := congrArg (valuation k) e
    rw [map_one, map_mul] at e'
    rw [Units.val_mul, Units.val_mul] at e'
    calc (1 : ValueGroupWithZero k) = _ := e'
      _ ≤ valuation k c * 1 := by gcongr
      _ = valuation k c := mul_one _
  have hc'1 : valuation k c' ≤ 1 := by
    have e : valuation k c * valuation k c' = 1 := by rw [← map_mul, hcc, map_one]
    calc valuation k c' = 1 * valuation k c' := (one_mul _).symm
      _ ≤ valuation k c * valuation k c' := by gcongr
      _ = 1 := e

  have hinv : (a ^ r)⁻¹ = (q⁻¹ * (a ^ r')⁻¹ * p⁻¹) * z⁻¹ := by
    rw [h]; group
  have hle : (valuation k (t : k))⁻¹ ^ r ≤ (valuation k (t : k))⁻¹ ^ r' := by
    have e := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i₁ i₁) hinv
    simp only [Units.val_mul (b := z⁻¹), ← hc'] at e
    rw [coe_inv_pow_of_diag hδ0 ha, diagonal_apply_eq, h₁, Matrix.scalar_apply,
      Matrix.mul_diagonal] at e
    have b := entry_bound (val_le_one_of_mem (inv_mem hq)) (val_le_one_of_mem (inv_mem hp)) hB' i₁ i₁
    have e' := congrArg (valuation k) e
    rw [map_pow, map_inv₀, map_mul, Units.val_mul, Units.val_mul] at e'
    rw [e']
    calc _ ≤ (valuation k (t : k))⁻¹ ^ r' * 1 := by gcongr
      _ = _ := mul_one _
  exact (pow_le_pow_iff_right₀ ((one_lt_inv₀ (zero_lt_iff.2 hvt0)).2 ht)).1 hle

theorem coe_leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : Matrix (Fin N) (Fin N) k) =
      diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      simp only [Zl.JC.zj, Zl.JC.blockIdx, Equiv.symm_apply_apply]
      split_ifs <;> simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      simp only [Zl.JC.zj]
      split_ifs
      · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, diagonal_apply_ne _ hil]
      · simp [Matrix.one_apply_ne hil]
  · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, l⟩ := fun e =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem le_of_mk_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hpos : ∀ a, 0 < d a) (t : kˣ)
    (ht : valuation k (t : k) < 1) (j : Fin h) (hj : j.val + 1 < h) (m : ℕ)
    {x y x' y' : GL (Fin N) k} (hx : x ∈ congruenceSubgroup k N m)
    (hy : y ∈ congruenceSubgroup k N m) (hx' : x' ∈ congruenceSubgroup k N m)
    (hy' : y' ∈ congruenceSubgroup k N m) {r r' : ℕ}
    (e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
      QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y')) :
    r' ≤ r := by
  have hz := QuotientGroup.eq.1 e
  have hK := congruenceSubgroup_le k N m
  have heq := eq_central_mul hz
  refine le_of_eq_central_mul (δ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1) t ht
    (fun i => ?_) (i₁ := stdBlocks d hd ⟨j, ⟨0, hpos j⟩⟩)
    (i₂ := stdBlocks d hd ⟨⟨j.val + 1, hj⟩, ⟨0, hpos _⟩⟩) ?_ ?_
    (coe_leviEmb_zj d hd t j)
    (mul_mem (inv_mem (hK hx')) (hK hx)) (mul_mem (hK hy) (inv_mem (hK hy'))) hz heq
  · by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · simp [Zl.JC.blockIdx]
  · have : ¬ (⟨j.val + 1, hj⟩ : Fin h) ≤ j := by
      rw [Fin.le_def]; simp
    simp [Zl.JC.blockIdx, this]

theorem images_measurable_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (isOpen_doubleCoset _ (isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm (le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))

end GlobalTheory.CompanionTheory.ContractingCosets

end
