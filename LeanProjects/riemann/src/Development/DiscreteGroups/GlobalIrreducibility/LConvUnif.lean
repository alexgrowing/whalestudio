import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvUnifB

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic GroundTheory.Automorphic.Cartan GroundTheory.Automorphic.Parabolic Matrix

section Hop

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) F) V}
  (hρ : GroundTheory.Automorphic.IsSmooth ρ) {r : ℕ}
  (hKc : IsCompact (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))
  (hKo : IsOpen (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))

include hρ hKc hKo

theorem hop_diagPow_mul (hr : 1 ≤ r) {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν) :
    hop ρ hρ hKc hKo (diagPow F n μ) * hop ρ hρ hKc hKo (diagPow F n ν) =
      hop ρ hρ hKc hKo (diagPow F n (μ + ν)) := by
  rw [diagPow_add]
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := dominant_conj hr hμ hν hκ
  have hbc : ρ (b * c) w = w := hw _ (mul_mem hb hc)
  rw [h, show a * (diagPow F n μ * diagPow F n ν) * b * c =
      a * ((diagPow F n μ * diagPow F n ν) * (b * c)) by group,
    map_mul, Module.End.mul_apply, fixedProj_apply_act hρ hKc hKo ha, map_mul,
    Module.End.mul_apply, hbc]

theorem hop_integral_mul {k : GL (Fin n) F} (hk : k ∈ GLnLocal.integralGL F n)
    (g : GL (Fin n) F) :
    hop ρ hρ hKc hKo k * hop ρ hρ hKc hKo g = hop ρ hρ hKc hKo (k * g) := by
  refine hop_mul hρ hKc hKo fun w _ κ hκ => ?_
  rw [show k * κ * g = (k * κ * k⁻¹) * (k * g) by group, map_mul, Module.End.mul_apply,
    fixedProj_apply_act hρ hKc hKo (GLnLocal.conj_mem_congruenceSubgroup F n hk hκ)]

theorem hop_mul_integral (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ GLnLocal.integralGL F n) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo k = hop ρ hρ hKc hKo (g * k) := by
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  rw [show g * κ * k = (g * k) * (k⁻¹ * κ * k⁻¹⁻¹) by group, map_mul, Module.End.mul_apply,
    hw _ (GLnLocal.conj_mem_congruenceSubgroup F n (inv_mem hk) hκ)]

local notation "Kr" => GLnLocal.congruenceSubgroup F n r
local notation "K0" => GLnLocal.integralGL F n
local notation "W" => fixedVectors ρ (GLnLocal.congruenceSubgroup F n r)
local notation "T" => hop ρ hρ hKc hKo

theorem finrank_le_of_commBound (hr : 1 ≤ r) [ρ.IsIrreducible] [FiniteDimensional ℂ W]
    [Fintype (K0 ⧸ (Kr).subgroupOf K0)] {c : ℕ}
    (hc : ∀ a : Fin (n + 1) → Module.End ℂ W, (∀ i j, a i * a j = a j * a i) →
      2 * Fintype.card (K0 ⧸ (Kr).subgroupOf K0) ^ 2 *
          Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ W ^ 2 + c * Module.finrank ℂ W) :
    Module.finrank ℂ W ≤ c := by
  classical
  by_cases h0 : Module.finrank ℂ W = 0
  · rw [h0]; exact Nat.zero_le _
  have hpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero h0
  have : Nontrivial W := Module.finrank_pos_iff.1 hpos
  have hspan := span_hop_eq_top hρ hKc hKo
  let a : Fin (n + 1) → Module.End ℂ W := fun i => T (diagPow F n (gen n i))
  have hcomm : ∀ i j, a i * a j = a j * a i := fun i j => by
    simp only [a]
    rw [hop_diagPow_mul hρ hKc hKo hr (gen_dominant n i) (gen_dominant n j),
      hop_diagPow_mul hρ hKc hKo hr (gen_dominant n j) (gen_dominant n i), add_comm]
  let C := Algebra.adjoin ℂ (Set.range a)
  have hTC : ∀ μ, IsDominant μ → T (diagPow F n μ) ∈ C := by
    refine dom_induct (fun μ => T (diagPow F n μ) ∈ C) ?_ ?_ ?_
    · show T (diagPow F n 0) ∈ C
      rw [diagPow_zero, hop_one]
      exact C.one_mem
    · intro i
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro μ ν hμ hν h1 h2
      show T (diagPow F n (μ + ν)) ∈ C
      rw [← hop_diagPow_mul hρ hKc hKo hr hμ hν]
      exact C.mul_mem h1 h2
  let P : (K0 ⧸ (Kr).subgroupOf K0) → Module.End ℂ W :=
    fun q => T ((Quotient.out q : K0) : GL (Fin n) F)
  have hP : ∀ k (hk : k ∈ K0), P (QuotientGroup.mk ⟨k, hk⟩) = T k := by
    intro k hk
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((Kr).subgroupOf K0) (⟨k, hk⟩ : K0)
    show T ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K0 ⧸ (Kr).subgroupOf K0) : K0) :
      GL (Fin n) F) = T k
    rw [hh, Subgroup.coe_mul, ← hop_mul_integral hρ hKc hKo _ ((h : K0)).2,
      hop_of_mem hρ hKc hKo (Subgroup.mem_subgroupOf.1 h.2), mul_one]
  have hCfin : FiniteDimensional ℂ C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  let Φ : ((K0 ⧸ (Kr).subgroupOf K0) × (K0 ⧸ (Kr).subgroupOf K0) → C) →ₗ[ℂ] Module.End ℂ W :=
    ∑ p, (LinearMap.mulLeft ℂ (P p.1)) ∘ₗ (LinearMap.mulRight ℂ (P p.2)) ∘ₗ
      C.val.toLinearMap ∘ₗ LinearMap.proj p
  have hΦ : ∀ f, Φ f = ∑ p, P p.1 * (((f p : C) : Module.End ℂ W) * P p.2) := by
    intro f
    rw [LinearMap.sum_apply]
    rfl
  have hrange : Set.range T ⊆ LinearMap.range Φ := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨μ, hμ, k1, hk1, k2, hk2, hg⟩ := exists_eq_mul_diagPow_mul F n g
    refine ⟨Pi.single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)
      ⟨_, hTC μ hμ⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)]
    · rw [Pi.single_eq_same]
      show P (QuotientGroup.mk ⟨k1, hk1⟩) * (T (diagPow F n μ) * P (QuotientGroup.mk ⟨k2, hk2⟩)) = T g
      rw [hP, hP, hg, mul_assoc, hop_mul_integral hρ hKc hKo _ hk2,
        hop_integral_mul hρ hKc hKo hk1]
    · intro p _ hp
      rw [Pi.single_eq_of_ne hp]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have htop : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    exact hrange
  have hdim := LinearMap.finrank_range_le Φ
  rw [htop, finrank_top, Module.finrank_linearMap, Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul] at hdim
  have hcb := hc a hcomm
  have h2 : Module.finrank ℂ W * Module.finrank ℂ W ≤ c * Module.finrank ℂ W := by
    nlinarith [hdim, hcb]
  exact Nat.le_of_mul_le_mul_right h2 hpos

end Hop

end DiscreteGroups.sglob.LConvU

namespace DiscreteGroups.sglob.LConv

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic DiscreteGroups.sglob.LConvU

theorem unifOfComm : UnifOfComm := by
  intro hCB k _ _ _ _ m K hK
  classical
  obtain ⟨r0, -, hr0⟩ := (GLnLocal.hasBasis_nhds_one k m).mem_iff.1 (hK.mem_nhds K.one_mem)
  obtain ⟨r, hr, hrr⟩ : ∃ r, 1 ≤ r ∧ r0 ≤ r := ⟨max r0 1, le_max_right _ _, le_max_left _ _⟩
  have hKrK : GLnLocal.congruenceSubgroup k m r ≤ K := fun x hx =>
    hr0 (GLnLocal.congruenceSubgroup_antitone k m hrr hx)
  have hKc := GLnLocal.isCompact_congruenceSubgroup k m r
  have hKo := GLnLocal.isOpen_congruenceSubgroup k m r
  have : CompactSpace (GLnLocal.integralGL k m) :=
    isCompact_iff_compactSpace.mp (GLnLocal.isCompact_integralGL k m)
  have hHo : IsOpen (((GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m) :
      Subgroup (GLnLocal.integralGL k m)) : Set (GLnLocal.integralGL k m)) :=
    hKo.preimage continuous_subtype_val
  have : Finite (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Fintype.ofFinite _
  obtain ⟨c, hc⟩ := hCB (m + 1) (2 * Fintype.card (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) ^ 2)
  refine ⟨c, fun V _ _ ρ hρs hρi => ?_⟩
  have hρ : GroundTheory.Automorphic.IsSmooth ρ := fun v => hρs v
  have : ρ.IsIrreducible := hρi
  have hfin : FiniteDimensional ℂ (fixedVectors ρ (GLnLocal.congruenceSubgroup k m r)) :=
    (isAdmissible_of_isIrreducible hρ).2 _ hKc hKo
  have hle : GlobalTheory.PRep.fixed ρ K ≤ fixedVectors ρ (GLnLocal.congruenceSubgroup k m r) := by
    intro v hv κ hκ
    have := hv ⟨κ, hKrK hκ⟩
    simpa using this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)).trans
    (finrank_le_of_commBound hρ hKc hKo hr (c := c) fun a ha => hc _ a ha)

end DiscreteGroups.sglob.LConv
