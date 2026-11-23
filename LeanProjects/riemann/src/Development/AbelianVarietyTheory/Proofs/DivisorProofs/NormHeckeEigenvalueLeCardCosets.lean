import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

namespace GlobalTheory.LFun

theorem norm_le_card_of_heckeVec_eq_smul :
    ∀ (G : Type) [Group G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) →
      (∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) → ∀ (h : G → ℂ) (x : V) (c : ℂ), (∀ g, ‖h g‖ ≤ 1) →
      {q : G ⧸ K | h q.out ≠ 0}.Finite → x ≠ 0 → GlobalTheory.LFun.heckeVec ρ K h x = c • x →
      ‖c‖ ≤ Nat.card {q : G ⧸ K // h q.out ≠ 0} := by
  intro G _ K V _ _ ρ Bf hsym hpos hinv h x c hh hfin hx hc
  classical
  have hnn : ∀ y, 0 ≤ (Bf y y).re := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  let core : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by rw [hsym x y]; simp
      re_inner_nonneg := hnn
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have cs : ∀ y, ‖Bf x y‖ * ‖Bf y x‖ ≤ (Bf x x).re * (Bf y y).re :=
    fun y => @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ core x y
  have hr : 0 < (Bf x x).re := hpos x hx
  have hb : ∀ g, ‖Bf x (ρ g x)‖ ≤ (Bf x x).re := by
    intro g
    have h1 := cs (ρ g x)
    rw [hinv, hsym x (ρ g x), RCLike.norm_conj] at h1
    nlinarith [norm_nonneg (Bf x (ρ g x))]
  have hxx : ‖Bf x x‖ = (Bf x x).re := by
    have e : (starRingEnd ℂ) (Bf x x) = Bf x x := (hsym x x).symm
    rw [RCLike.conj_eq_iff_re] at e
    rw [← e]
    simp [abs_of_pos hr]
  set S := hfin.toFinset
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ S := by
    intro q hq
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ S, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  have key : c * Bf x x = ∑ q ∈ S, h q.out * Bf x (ρ q.out x) := by
    rw [← smul_eq_mul, ← map_smul, ← hc, hsum, map_sum]
    simp
  have hcard : Nat.card {q : G ⧸ K // h q.out ≠ 0} = S.card :=
    Nat.card_eq_card_finite_toFinset hfin
  have hle : ‖c‖ * (Bf x x).re ≤ (S.card : ℝ) * (Bf x x).re := by
    calc ‖c‖ * (Bf x x).re = ‖c * Bf x x‖ := by rw [norm_mul, hxx]
      _ = ‖∑ q ∈ S, h q.out * Bf x (ρ q.out x)‖ := by rw [key]
      _ ≤ ∑ q ∈ S, ‖h q.out * Bf x (ρ q.out x)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, (Bf x x).re := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul]
        calc ‖h q.out‖ * ‖Bf x (ρ q.out x)‖ ≤ 1 * (Bf x x).re :=
              mul_le_mul (hh _) (hb _) (norm_nonneg _) zero_le_one
          _ = (Bf x x).re := one_mul _
      _ = (S.card : ℝ) * (Bf x x).re := by simp
  rw [hcard]
  exact le_of_mul_le_mul_right hle hr

end GlobalTheory.LFun
