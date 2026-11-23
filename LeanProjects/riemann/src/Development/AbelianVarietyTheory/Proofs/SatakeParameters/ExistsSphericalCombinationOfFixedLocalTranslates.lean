import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphAvg

section Abstract

variable {G : Type} [Group G]

open GlobalTheory.SphLabelOps

theorem finiteIndex_stab {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) :
    (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
  have hfin : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K)).Finite := by
    refine (R.finite_toSet.image (fun γ => (QuotientGroup.mk γ : G ⧸ K))).subset ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨γ, ⟨hγ, e⟩, -⟩ := hR.2 ((k : G) * g) ⟨k, k.2, 1, one_mem _, by simp⟩
    refine ⟨γ, hγ, ?_⟩
    show (QuotientGroup.mk γ : G ⧸ K) = (k : G) • (QuotientGroup.mk g : G ⧸ K)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    exact e
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'

theorem mem_of_stab {K : Subgroup G} {g : G} {n : K} (hn : n ∈ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :
    g⁻¹ * (n : G) * g ∈ K := by
  have h : ((n : G) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk g := hn
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  have := inv_mem h
  convert this using 1
  group

theorem card_pos {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) : 0 < R.card := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 g ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact Finset.card_pos.2 ⟨γ, hγ⟩

theorem fixed_comb {K : Subgroup G} {ι : Type} (s : Finset ι) (g : ι → G) (R : ι → Finset G)
    (hR : ∀ i ∈ s, Reps K (g i) (R i)) (a : ι → ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u)
    (hw : ∀ k ∈ K, π k (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π (g i) u) :
    ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, (a i / ((R i).card : ℂ)) • ∑ γ ∈ R i, π γ u := by
  classical
  have fix : ∀ x, ∀ l ∈ K, π (x * l) u = π x u := fun x l hl => by
    rw [map_mul, Module.End.mul_apply, hu l hl]
  let St : ι → Subgroup K := fun i => MulAction.stabilizer K (QuotientGroup.mk (g i) : G ⧸ K)
  have hSt : (⨅ i ∈ s, St i).FiniteIndex := Subgroup.finiteIndex_iInf' St fun i hi => finiteIndex_stab (hR i hi)
  let N : Subgroup K := (⨅ i ∈ s, St i).normalCore
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hN : ∀ i ∈ s, ∀ n ∈ N, ∀ x : G, π (x * (n : G) * g i) u = π (x * g i) u := by
    intro i hi n hn x
    have h1 : n ∈ St i := (iInf₂_le i hi : (⨅ i ∈ s, St i) ≤ St i) (Subgroup.normalCore_le _ hn)
    have := fix (x * g i) _ (mem_of_stab h1)
    rw [← this]
    congr 1
    group
  let T : ι → M := fun i => ∑ q : K ⧸ N, π ((q.out : G) * g i) u

  have hT : ∀ i ∈ s, ∀ k₁ ∈ K, ∑ q : K ⧸ N, π ((q.out : G) * k₁ * g i) u = T i := by
    intro i hi k₁ hk₁
    have e := Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N))
      (fun q => π (((q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out : G) * g i) u)
      (fun q => π ((q.out : G) * g i) u) (fun q => rfl)
    refine Eq.trans ?_ e
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : (q.out * ⟨k₁, hk₁⟩)⁻¹ * (q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have := hN i hi _ hq ((q.out : G) * k₁)
    rw [← this]
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  have hC : ∀ i ∈ s, ((R i).card : ℂ) • T i = (Fintype.card (K ⧸ N) : ℂ) • ∑ γ ∈ R i, π γ u := by
    intro i hi
    have e1 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ γ ∈ R i, T i := by
      refine Finset.sum_congr rfl fun γ hγ => ?_
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := (hR i hi).1 γ hγ
      rw [← hT i hi k₁ h₁]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← fix ((q.out : G) * k₁ * g i) k₂ h₂]
      congr 1
      group
    have e2 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ q : K ⧸ N, ∑ γ ∈ R i, π γ u := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => (hR i hi).sum_eq (hR i hi) q.out.2 (fun x => π x u) fix
    rw [e1, Finset.sum_const, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      ← Nat.cast_smul_eq_nsmul ℂ] at e2
    exact e2
  have hQ : (Fintype.card (K ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have main : (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, a i • T i := by
    have e : ∀ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π ((q.out : G) * g i) u := by
      intro q
      simp only [map_sum, map_smul, map_mul, Module.End.mul_apply]
    calc (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u
        = ∑ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) := by
          rw [Nat.cast_smul_eq_nsmul ℂ, ← Finset.card_univ, ← Finset.sum_const]
          exact Finset.sum_congr rfl fun q _ => (hw _ q.out.2).symm
      _ = ∑ i ∈ s, a i • T i := by
          simp only [e, T, Finset.smul_sum]
          exact Finset.sum_comm
  refine smul_right_injective M hQ ?_
  simp only
  rw [main, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_comm, ← hC i hi, smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (card_pos (hR i hi)).ne')]

end Abstract

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

open GlobalTheory.SphLabelOps GlobalTheory.IdemSupport

theorem fixed_comb_eq_opOf : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → (∀ k ∈ hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  classical
  intro D V P e f h a ha
  obtain ⟨K, hK⟩ := exists_hyp V P
  obtain ⟨-, ϖ, -, h1, h2⟩ := exists_real_unif D P
  have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1
  have hd : ∀ g, ∃ d, SuppF V f g → Reps K g (rep V P d) := by
    intro g
    by_cases hg : SuppF V f g
    · obtain ⟨d, hd, hD⟩ := exists_divAt V he (tie_of_isPrimeIdem h) h1 h2 g
      exact ⟨d, fun _ => reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep (isLab_of_divAt h h1 h2 hd hg hD))⟩
    · exact ⟨[], fun h' => absurd h' hg⟩
  choose d hd using hd
  refine ⟨∑ g ∈ a.support, Finsupp.single (d g) (a g / ((rep V P (d g)).card : ℂ)), ?_⟩
  intro M _ _ π u hu hw
  have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (by rw [hK]; exact hk)
  have hw' : ∀ k ∈ K, π k (∑ g ∈ a.support, a g • π (id g) u) = ∑ g ∈ a.support, a g • π (id g) u :=
    fun k hk => hw k (by rw [hK]; exact hk)
  rw [Finsupp.sum]
  refine (fixed_comb a.support id (fun g => rep V P (d g)) (fun g hg => hd g (ha g hg)) a π u hu' hw').trans ?_
  rw [opOf, ← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul]), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp), LinearMap.smul_apply, LinearMap.sum_apply]

end GlobalTheory.SphAvg
