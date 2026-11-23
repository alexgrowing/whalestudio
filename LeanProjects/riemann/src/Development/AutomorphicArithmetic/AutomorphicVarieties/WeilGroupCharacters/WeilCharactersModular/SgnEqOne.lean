import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

open Classical in
private noncomputable def sgn {Γ : Type} [Group Γ] (H : Subgroup Γ) (h : H.index = 2) : Γ →* ℤˣ :=
  MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => by
    simp only [Subgroup.mul_mem_iff_of_index_two h]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]

theorem UpperTheory.V.W.levEx :
    LevEx := by
  intro l _ L Ω _ _ _ _ _ _ s S' hfin hsub hsplit
  have key : ∀ σ : G (Lp L) Ω, σ ∈ (resP L Ω).range ↔
      ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x := by
    intro σ
    constructor
    · rintro ⟨τ, rfl⟩ x
      exact τ.commutes x
    · intro h
      exact ⟨{ σ with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩
  have hrange : (resP L Ω).range = (AlgEquiv.restrictNormalHom (F := Lp L) (K₁ := Ω) L).ker := by
    ext σ
    rw [key, MonoidHom.mem_ker]
    change _ ↔ σ.restrictNormal L = 1
    constructor
    · intro h
      refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
      rw [AlgEquiv.restrictNormal_commutes, h x, AlgEquiv.one_apply]
    · intro h x
      rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  have hidx : (resP L Ω).range.index = 2 := by
    rw [hrange, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := Lp L) (K₁ := L) Ω),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hc : s.c ∉ (resP L Ω).range := by
    intro hm
    obtain ⟨j, hj⟩ := s.hc
    apply IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap L Ω))
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, (key _).1 hm x]
  have hsg : ∀ g, sgn _ hidx g = 1 ↔ g ∈ (resP L Ω).range := by
    intro g
    simp only [sgn, MonoidHom.mk'_apply]
    split_ifs with h
    · simp [h]
    · simp only [h, iff_false]
      decide
  have hclosed : IsClosed ((resP L Ω).range : Set (G (Lp L) Ω)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range UpperTheory.V.W.continuous_resP).isClosed
  have hnorm : (resP L Ω).range.Normal := by
    rw [hrange]
    infer_instance
  have hNS : NS Ω S' ≤ (resP L Ω).range := by
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    exact s.unr A v hA hσA
  have hcycClosed : IsClosed ((cycZ (Lp L) Ω l).ker : Set (G (Lp L) Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ (Lp L) Ω l)
  have hNS2 : NS Ω S' ≤ (cycZ (Lp L) Ω l).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ hcycClosed
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hl : ((l : 𝓞 (Lp L))) ∉ v.asIdeal := fun h => hv (hsub (Or.inl h))
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hA hl hσA
  have hNSη : NS Ω S' ≤ (sgn _ hidx).ker := fun σ hσ => (hsg σ).2 (hNS hσ)
  let η : GS Ω S' →* ℤˣ := QuotientGroup.lift (NS Ω S') (sgn _ hidx) hNSη
  let ε : GS Ω S' →* ℤ_[l]ˣ := QuotientGroup.lift (NS Ω S') (cycZ (Lp L) Ω l) hNS2
  have hηg : ∀ g, η (toGS Ω S' g) = sgn _ hidx g := fun g => QuotientGroup.lift_mk _ hNSη g
  have hpre : (QuotientGroup.mk ⁻¹' (η.ker : Set (GS Ω S')) : Set (G (Lp L) Ω)) =
      ((resP L Ω).range : Set (G (Lp L) Ω)) := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [← hsg g]
    exact Iff.rfl
  haveI : (resP L Ω).range.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  refine ⟨⟨S', hfin, hsub, hsplit, η, ?_, ?_, ?_, ε, ?_, ?_⟩, rfl⟩
  · intro g
    rw [hηg, hsg]
  · rw [← (QuotientGroup.isQuotientMap_mk (NS Ω S')).isOpen_preimage, hpre]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed
  · rw [hηg]
    simp only [sgn, MonoidHom.mk'_apply, if_neg hc]
  · exact MonoidHom.ext fun g => QuotientGroup.lift_mk _ hNS2 g
  · exact (QuotientGroup.isQuotientMap_mk (NS Ω S')).continuous_iff.mpr
      (by exact continuous_cycZ (Lp L) Ω l)
