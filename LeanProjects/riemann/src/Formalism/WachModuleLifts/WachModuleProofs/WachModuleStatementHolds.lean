import Formalism.WachModuleLifts.StatementW

noncomputable section

namespace Formalism.CL.W

section Lift
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']

lemma Q_φ (W : WachMod B η D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := W.φ_N x hx

end Lift

section Claim
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]

def QS (W : WachMod B η D) : Submodule ℤ_[p] D where
  carrier := {y | B.q ^ η • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.q ^ η • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.q ^ η • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.q ^ η • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy

end Claim

section Gamma
theorem gammaImageProduct_holds : GammaOnto := by
  intro p _ A _ _ B η D _ _ _ _ W u a hyp
  suffices h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.π₀ • n) =
        (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (j + 1) • z' from h a le_rfl
  intro j
  induction j with
  | zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ j ih =>
    intro hj n hn
    obtain ⟨x, hx, m, hm, he⟩ := ih (by omega) n hn
    obtain ⟨n', hn', hg⟩ := hyp (j+1) (by omega) hj m hm
    refine ⟨(1 - u^(j+1)) • x - B.π₀ ^ j • m, ?_, n', hn', ?_⟩
    · exact W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.π₀ • ((1 - u^(j+1)) • x - B.π₀ ^ j • m)
          = (1 - u^(j+1)) • (B.π₀ • x) - B.π₀ ^ (j+1) • m := by
        rw [smul_sub, smul_comm, smul_smul, ← pow_succ']
      rw [e1, map_sub, LinearMap.map_smul, hg]
      have e2 : B.π₀ ^ (j + 1 + 1) • n' = B.π₀ ^ (j+1+1) • n' := rfl
      simp only [smul_sub, smul_add, sub_smul, one_smul]
      abel
end Gamma

section Wit
open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev K := FractionRing (Polynomial ℤ_[p])

example : IsScalarTower ℤ_[p] (Polynomial ℤ_[p]) (K p) := inferInstance

def polyW : WachMod (polyBase p) 0 (K p) where
  N := LinearMap.range (Algebra.linearMap (Polynomial ℤ_[p]) (K p))
  φ := 0
  γ := LinearMap.id
  φ_smul := by intros; simp
  γ_smul := by intros; simp [polyBase]
  comm := by intros; simp
  π₀_inj := by
    intro x hx
    simp only [polyBase, Algebra.smul_def] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd ((IsFractionRing.injective (Polynomial ℤ_[p]) (K p)) (h.trans (map_zero _).symm)) X_ne_zero
    · exact h
  q_bij := by
    have hne : (algebraMap (Polynomial ℤ_[p]) (K p)) (X + C (p : ℤ_[p])) ≠ 0 := by
      intro h
      have := (IsFractionRing.injective (Polynomial ℤ_[p]) (K p)) (h.trans (map_zero _).symm)
      exact X_add_C_ne_zero _ this
    refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap _ (K p) (X + C (p : ℤ_[p])))⁻¹ * b, ?_⟩⟩
    · simp only [polyBase, Algebra.smul_def] at h
      exact mul_left_cancel₀ hne h
    · simp only [polyBase, Algebra.smul_def]; field_simp
  φ_N := by intro x hx; simp
  γ_N := by intro x hx; exact ⟨0, Submodule.zero_mem _, by simp⟩
  γ_qN := by intro y hy; exact ⟨0, by simp, by simp⟩

theorem polyW_nondeg : (polyW p).N ≠ ⊥ ∧ ¬ IsUnit (polyBase p).π₀ := by
  constructor
  · intro h
    have : (1 : K p) ∈ (polyW p).N := ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at this; exact one_ne_zero this
  · simp only [polyBase]; exact Polynomial.not_isUnit_X

end Wit

theorem wach_module_nonempty : WachNonempty := fun p _ => ⟨polyW p, polyW_nondeg p⟩

end Formalism.CL.W
