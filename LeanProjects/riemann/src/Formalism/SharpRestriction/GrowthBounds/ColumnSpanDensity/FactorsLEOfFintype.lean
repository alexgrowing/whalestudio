import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudBoundOfPropAndWeylDimension
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NLeDAll
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoSumBoundOfMapsSplitting
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def LemmaSMat : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O), z1 ≠ 0 → z2 ≠ 0 →
    ∀ (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O),
    ∃ (r s : ℕ), r + s = σ ∧
      (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O),
        P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
      (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O)
        (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
        Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'')
          (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O))

def LatRetract : Prop :=
  ∀ (O K V V' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V']
    [Module K V'] [Module O V'] [IsScalarTower O K V'] (ι ι' : Type) [Fintype ι] [Fintype ι']
    (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V'),
    (∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) →
    ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧
      ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b)

private theorem ordW_alg_lemma {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (z : O)
    (hz : z ≠ 0) :
    ordW (algebraMap O (KK O) z) = (((IsDiscreteValuationRing.addVal O z).toNat : ℤ) : WithTop ℤ) := by
  have hx : algebraMap O (KK O) z ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hz
  have key : ∀ ab : O × nonZeroDivisors O,
      algebraMap O (KK O) z * algebraMap O (KK O) (ab.2 : O) = algebraMap O (KK O) ab.1 →
      ((IsDiscreteValuationRing.addVal O ab.1).toNat : ℤ) - (IsDiscreteValuationRing.addVal O (ab.2 : O)).toNat
        = (IsDiscreteValuationRing.addVal O z).toNat := by
    rintro ⟨a, b, hb⟩ h
    have hb0 : (b : O) ≠ 0 := nonZeroDivisors.ne_zero hb
    have h' : z * b = a := IsFractionRing.injective O (KK O) (by simpa using h)
    subst h'
    simp only
    rw [AddValuation.map_mul]
    have t1 : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
      simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hz
    have t2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
      simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb0
    rw [ENat.toNat_add t1 t2]
    push_cast
    ring
  unfold ordW
  rw [if_neg hx]
  exact congrArg _ (key _ (Classical.choose_spec (ordW._proof_1 (algebraMap O (KK O) z))))

theorem vLEO_one {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {D : ℝ} (hD : 0 ≤ D) :
    vLEO p (1 : O) D := by
  refine ⟨0, ?_, by simpa using hD⟩
  unfold vO vK
  rw [ordW_alg_lemma (1 : O) one_ne_zero]
  simp

theorem vLEO_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {z1 z2 : O}
    (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) {D1 D2 : ℝ} (v1 : vLEO p z1 D1) (v2 : vLEO p z2 D2) :
    vLEO p (z1 * z2) (D1 + D2) := by
  obtain ⟨q1, e1, l1⟩ := v1
  obtain ⟨q2, e2, l2⟩ := v2
  rw [vO_eq h1] at e1
  rw [vO_eq h2] at e2
  have e1' := WithTop.coe_injective e1
  have e2' := WithTop.coe_injective e2
  have hv1 : IsDiscreteValuationRing.addVal O z1 ≠ ⊤ := fun h => h1 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hv2 : IsDiscreteValuationRing.addVal O z2 ≠ ⊤ := fun h => h2 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨q1 + q2, ?_, by push_cast; linarith⟩
  rw [vO_eq (mul_ne_zero h1 h2), IsDiscreteValuationRing.addVal_mul, ENat.toNat_add hv1 hv2, ← e1', ← e2']
  congr 1
  push_cast
  ring

theorem factorsLE_of_fintype {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] (p : ℕ) (be : V → V' → Kf)
    (A : Submodule O V) (A' : Submodule O V') {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → V) (y : ι → V')
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O) (hz : z ≠ 0) {D : ℝ} (hv : vLEO p z D)
    (h : ∀ i j, be (x i) (y j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' (Fintype.card ι) D := by
  right
  refine ⟨fun k => x ((Fintype.equivFin ι).symm k), fun k => y ((Fintype.equivFin ι).symm k),
    fun k => hx _, fun k => hy _, z, 1, hz, hv, ?_⟩
  intro i j
  simp [Matrix.one_apply, h, (Fintype.equivFin ι).symm.injective.eq_iff]

theorem scale_anti {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (w : O) {c c' : ℕ} (h : c' ≤ c) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ (c : ℤ)) M ≤ scale (algebraMap O Kf w ^ (c' : ℤ)) M := by
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨(w ^ (c - c')) • m, M.smul_mem _ hm, ?_⟩
  simp only [zpow_natCast, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  rw [← algebraMap_smul Kf (w ^ (c - c')) m, smul_smul, map_pow, ← pow_add, Nat.add_sub_cancel' h]

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem CCL_anti_c {c c' : ℕ} (h : c' ≤ c) (t : ℕ) (e : Edge R.W R.Qq (m + 1)) :
    CCL R lam0 t c e ≤ CCL R lam0 t c' e := by
  unfold CCL
  exact inf_le_inf_left _ (iInf_mono fun e' => iInf_mono fun _ => scale_anti R.w h _)

theorem wit_of_factors {A : Submodule R.O (Vsp R.Kf lam0)} {A' : Submodule R.O (Module.Dual R.Kf (Vsp R.Kf lam0))}
    {n : ℕ} {D : ℝ} (hD : 0 ≤ D) (h : FactorsLE p (be (Kf := R.Kf) p 1 lam0) A A' n D) :
    ∃ (x : Fin n → Vsp R.Kf lam0) (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z : R.O),
      (∀ i, x i ∈ A) ∧ (∀ i, y i ∈ A') ∧ z ≠ 0 ∧ vLEO p z D ∧
      ∀ i j, be p 1 lam0 (x i) (y j) = if i = j then algebraMap R.O R.Kf z else 0 := by
  rcases h with rfl | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact ⟨Fin.elim0, Fin.elim0, 1, fun i => i.elim0, fun i => i.elim0, one_ne_zero, vLEO_one hD,
      fun i => i.elim0⟩
  · refine ⟨x, fun j => ∑ l, M l j • y l, z, hx, fun j => A'.sum_mem fun l _ => A'.smul_mem _ (hy l),
      hz, hv, ?_⟩
    intro i j
    rw [← hM i j]
    simp only [be, LinearMap.sum_apply, LinearMap.smul_apply, Algebra.smul_def, mul_comm]

theorem be_mat {α β γ δ : Type*} [Fintype β] [Fintype γ] (u : β → Vsp R.Kf lam0)
    (v : γ → Module.Dual R.Kf (Vsp R.Kf lam0)) (G : Matrix β γ R.O)
    (hG : ∀ k k', be p 1 lam0 (u k) (v k') = algebraMap R.O R.Kf (G k k')) (P : Matrix α β R.O) (Q : Matrix γ δ R.O)
    (i : α) (l : δ) :
    be p 1 lam0 (∑ k, algebraMap R.O R.Kf (P i k) • u k) (∑ k', Q k' l • v k') =
      algebraMap R.O R.Kf ((P * G * Q) i l) := by
  have hG' : ∀ k k', ((p : R.Kf) ^ Ar 1 lam0) * v k' (u k) = algebraMap R.O R.Kf (G k k') := by
    intro k k'
    rw [← hG k k']
    simp only [be, map_smul, smul_eq_mul]
  unfold be
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Matrix.mul_apply, map_mul, smul_eq_mul, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← hG' k k']
  ring

end Clean

end Formalism.MainNotions.flipOneThree.Pf

end
