import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

namespace GlobalTheory.ExistsEigenvector

theorem exists_eigenvector {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {U : Set G} (hU : IsOpen U)
    (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθ : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hne : ∑ i, T i (y i) ≠ 0) (heq : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v := by
  classical
  have hone : θ 1 = 1 := hθ 1 h1 K.one_mem
  have hθne : ∀ a ∈ K, θ a ≠ 0 := fun a ha h0 => by
    have := hmul a ha a⁻¹ (K.inv_mem ha)
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup K :=
    { carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, fun i => ?_⟩
        · rw [Subgroup.coe_mul, hmul _ a.2 _ b.2, ha, hb, one_mul]
        · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := ⟨hone, fun i => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, fun i => ?_⟩
        · have := hmul _ a.2 _ (K.inv_mem a.2)
          rw [mul_inv_cancel, hone, ha, one_mul] at this
          exact this.symm
        · conv_lhs => rw [← ha' i]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
  have hHo : IsOpen (H : Set K) := by
    have ho : IsOpen ((fun k : K => (k : G)) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      (hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))).preimage continuous_subtype_val
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨h1, by simp⟩) ?_)
    rintro k ⟨hk, hk'⟩
    exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : K → ι → V := fun k i => (θ k)⁻¹ • ρ k (y i)
  have hf : ∀ a b : K, QuotientGroup.leftRel H a b → f a = f b := by
    intro a b hab
    obtain ⟨h, h'⟩ : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have e : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
    funext i
    simp only [f]
    rw [e, hmul _ a.2 _ (a⁻¹ * b).2, h, mul_one, map_mul, Module.End.mul_apply, h']
  let F : K ⧸ H → ι → V := fun q => Quotient.liftOn' q f hf
  have hF : ∀ (h : K) (q : K ⧸ H) (i : ι), ρ h (F q i) = θ h • F (h • q) i := by
    intro h q i
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ρ h ((θ k)⁻¹ • ρ k (y i)) = θ h • ((θ (h * k))⁻¹ • ρ (h * k) (y i))
      rw [hmul _ h.2 _ k.2, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_inv,
        mul_inv_cancel_left₀ (hθne _ h.2)]
  have hT : ∀ q : K ⧸ H, ∑ i, T i (F q i) = ∑ i, T i (y i) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ∑ i, T i ((θ k)⁻¹ • ρ k (y i)) = _
      simp only [map_smul]
      rw [← Finset.smul_sum, heq _ k.2, smul_smul, inv_mul_cancel₀ (hθne _ k.2), one_smul]
  have hex : ∃ i, ∑ q, F q i ≠ 0 := by
    by_contra hc
    have hc' : ∀ i, ∑ q, F q i = 0 := fun i => not_not.1 fun h => hc ⟨i, h⟩
    have h0 : ∑ i, T i (∑ q, F q i) = 0 := by simp [hc']
    simp only [map_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [hT] at h0
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 h0)
    · exact hne h0
  obtain ⟨i, hi⟩ := hex
  refine ⟨_, hi, fun h hh => ?_⟩
  rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun q _ => hF ⟨h, hh⟩ q i]
  exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (fun q : K ⧸ H => θ h • F q i)

end GlobalTheory.ExistsEigenvector
