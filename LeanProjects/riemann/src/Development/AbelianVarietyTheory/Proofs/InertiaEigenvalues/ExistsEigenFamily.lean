import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift

namespace GlobalTheory.EigenFamilyStabilizer

def stab {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (θ : G → ℂ)
    (h1 : θ 1 = 1) (hm : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (y : ι → V) : Subgroup K where
  carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
  one_mem' := ⟨by simpa using h1, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [Subgroup.coe_mul, hm _ a.2 _ b.2, ha, hb, one_mul]
    · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun i => ?_⟩
    · have := hm _ (a⁻¹).2 _ a.2
      rw [ha, mul_one, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, h1] at this
      exact this.symm
    · conv_lhs => rw [← ha' i]
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      simp

theorem exists_eigen_family : ∀ {G V W ι : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V] [inst_4 : Module ℂ V] [inst_5 : AddCommGroup W] [inst_6 : Module ℂ W] [inst_7 : Fintype ι] {ρ : Representation ℂ G V}, GlobalTheory.PRep.IsSmooth ρ → ∀ {K : Subgroup G}, IsCompact (↑K : Set G) → ∀ {U : Set G}, IsOpen U → (1 : G) ∈ U → ∀ (θ : G → ℂ), (∀ g ∈ U, g ∈ K → θ g = (1 : ℂ)) → (∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) → ∀ (T : ι → V →ₗ[ℂ] W) (y : ι → V), (∀ k ∈ K, ∑ i : ι, (T i : V → W) (((ρ : G → V →ₗ[ℂ] V) k : V → V) (y i)) = θ k • ∑ i : ι, (T i : V → W) (y i)) → ∃ (u : ι → V), (∀ (j : ι), ∀ h ∈ K, ((ρ : G → V →ₗ[ℂ] V) h : V → V) (u j) = θ h • u j) ∧ ∑ i : ι, (T i : V → W) (u i) = ∑ i : ι, (T i : V → W) (y i) := by
  intro G V W ι _ _ _ _ _ _ _ _ ρ hρ K hK U hU hU1 θ hθ hm T y hy
  classical
  have h1 : θ 1 = 1 := hθ 1 hU1 K.one_mem
  let H : Subgroup K := stab ρ K θ h1 hm y
  have hHo : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H (g := 1)
    have ho : IsOpen (U ∩ ⋂ i, {g : G | ρ g (y i) = y i}) :=
      hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))
    have ho' : IsOpen ((Subtype.val : K → G) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho'.mem_nhds ?_) ?_
    · refine ⟨hU1, Set.mem_iInter.2 fun i => ?_⟩
      simp
    · rintro k ⟨hk, hk'⟩
      exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : ι → K → V := fun j k => θ (k⁻¹ : K) • ρ k (y j)
  have hf : ∀ j (k : K) (s : K), s ∈ H → f j (k * s) = f j k := by
    intro j k s hs
    have hs' : θ (s⁻¹ : K) = 1 := (H.inv_mem hs).1
    simp only [f]
    rw [mul_inv_rev, Subgroup.coe_mul, hm _ (s⁻¹).2 _ (k⁻¹).2, hs', one_mul, Subgroup.coe_mul, map_mul,
      Module.End.mul_apply, hs.2 j]
  let F : ι → K ⧸ H → V := fun j q => f j q.out
  have hF : ∀ j (k : K), F j (k : K ⧸ H) = f j k := by
    intro j k
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul H k
    simp only [F]
    rw [hs, hf j k s s.2]
  have hact : ∀ j (h : K) (q : K ⧸ H), ρ h (F j q) = θ h • F j (h • q) := by
    intro j h q
    induction q using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hF, hF]
      simp only [f]
      rw [map_smul, smul_smul, mul_comm (θ h), ← hm _ ((h * k)⁻¹).2 _ h.2, ← Subgroup.coe_mul,
        Subgroup.coe_mul K h k, map_mul, Module.End.mul_apply]
      congr 3
      group
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun j => (Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q, F j q, fun j h hh => ?_, ?_⟩
  · rw [map_smul, map_sum, smul_comm]
    congr 1
    rw [Finset.sum_congr rfl fun q _ => hact j ⟨h, hh⟩ q, ← Finset.smul_sum]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (F j)
  · have hq : ∀ q, ∑ i, T i (F i q) = ∑ i, T i (y i) := by
      intro q
      simp only [F, f, map_smul]
      rw [← Finset.smul_sum, hy _ q.out.2, smul_smul, ← hm _ (q.out⁻¹).2 _ q.out.2, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, h1, one_smul]
    simp only [map_smul, map_sum]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

end GlobalTheory.EigenFamilyStabilizer
