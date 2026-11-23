import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TorsSatMult

open CategoryTheory UpperTheory.V.KH

private theorem torsSat_coeff {M ι : Type} [AddCommGroup M] (L : Set M) (v : ι → M)
    (hv : LinearIndependent ℤ v) (x : M) (hx : x ∈ Submodule.span ℤ (Set.range v))
    (n : ℤ) (hn : n ≠ 0) (hnx : n • x ∈ Submodule.span ℤ (Set.range v ∩ L)) :
    x ∈ Submodule.span ℤ (Set.range v ∩ L) := by
  have hS : Set.range v ∩ L = v '' (v ⁻¹' L) := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [hS] at hnx ⊢
  rw [Finsupp.mem_span_image_iff_linearCombination] at hnx ⊢
  obtain ⟨d, hd, hdx⟩ := hnx
  rw [← Finsupp.range_linearCombination] at hx
  obtain ⟨c, rfl⟩ := hx
  have hcd : d = n • c := by
    apply hv
    rw [hdx, map_smul]
  refine ⟨c, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hd ⊢
  intro i hi
  have := hd i hi
  rw [hcd, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero] at this
  exact this.resolve_left hn

private theorem torsSat_mult {M : Type} [AddCommGroup M] (L : Set M) (N : Submodule ℤ M)
    (h : ∀ x ∈ L, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N) (x : M) (hx : x ∈ Submodule.span ℤ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N :=
  _root_.UpperTheory.Reformulated.B.Qi35.torsSat_mult L N h x hx

private theorem torsSat_tors {M : Type} [AddCommGroup M] (N : Submodule ℤ M) (x : M)
    (hx : (Submodule.Quotient.mk x : M ⧸ N) ∈ AddCommGroup.torsion (M ⧸ N)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have hx' : IsOfFinAddOrder (Submodule.Quotient.mk x : M ⧸ N) := hx
  obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx'
  refine ⟨n, by exact_mod_cast hn.ne', ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, natCast_zsmul]
  exact h

theorem UpperTheory.V.KH.torsSat :
    ∀ (M ι : Type) [AddCommGroup M] [IsAddTorsionFree M] (L : Set M) (v : ι → M) (B : ℕ),
      LinearIndependent ℤ v →
      (∀ x ∈ L, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ (Set.range v ∩ L)) →
      CardLe (M ⧸ Submodule.span ℤ (Set.range v)) B → TorsLe (M ⧸ Submodule.span ℤ L) B := by
  intro M ι _ _ L v B hv hL hc
  obtain ⟨hfin, hB⟩ := hc
  choose lift hlift using Submodule.Quotient.mk_surjective (Submodule.span ℤ L)
  let f : AddCommGroup.torsion (M ⧸ Submodule.span ℤ L) → M ⧸ Submodule.span ℤ (Set.range v) :=
    fun t => Submodule.Quotient.mk (lift t.1)
  have hf : Function.Injective f := by
    intro t s hts
    have h1 : lift t.1 - lift s.1 ∈ Submodule.span ℤ (Set.range v) :=
      (Submodule.Quotient.eq _).1 hts
    have h2 : (Submodule.Quotient.mk (lift t.1 - lift s.1) : M ⧸ Submodule.span ℤ L) ∈
        AddCommGroup.torsion (M ⧸ Submodule.span ℤ L) := by
      rw [Submodule.Quotient.mk_sub, hlift, hlift]
      exact sub_mem t.2 s.2
    obtain ⟨n, hn, hnx⟩ := torsSat_tors _ _ h2
    obtain ⟨m, hm, hmx⟩ := torsSat_mult L _ hL _ hnx
    rw [smul_smul] at hmx
    have h3 := torsSat_coeff L v hv _ h1 _ (mul_ne_zero hm hn) hmx
    have h4 : lift t.1 - lift s.1 ∈ Submodule.span ℤ L :=
      Submodule.span_mono Set.inter_subset_right h3
    apply Subtype.ext
    rw [← hlift t.1, ← hlift s.1]
    exact (Submodule.Quotient.eq _).2 h4
  exact ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans hB⟩
