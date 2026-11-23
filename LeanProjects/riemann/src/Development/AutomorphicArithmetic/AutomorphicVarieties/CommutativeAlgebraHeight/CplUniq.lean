import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplIs
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevelOfCongruence

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cu_uniq {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (F G : R →+* T)
    (e : F.comp (algebraMap C R) = G.comp (algebraMap C R))
    (hF : maximalIdeal R ≤ J.comap F) (hG : maximalIdeal R ≤ J.comap G) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  obtain ⟨c, hc⟩ := h.dense n r
  have h1 : F (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow F n (Ideal.pow_right_mono hF n hc)
  have h2 : G (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow G n (Ideal.pow_right_mono hG n hc)
  have h3 : F (algebraMap C R c) = G (algebraMap C R c) := RingHom.congr_fun e c
  rw [Ideal.Quotient.eq]
  have := sub_mem h1 h2
  rw [map_sub, map_sub, h3] at this
  simpa using this

private theorem cu_ex {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T)
    (hf : x ≤ J.comap f) :
    ∃ F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F :=
  _root_.UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex h J f hf

private theorem cu_le {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x ≤ (maximalIdeal R).comap (algebraMap C R) := by
  have := h.comap_pow 1
  rw [pow_one, pow_one] at this
  exact this.ge

private theorem cu_map {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x.map (algebraMap C R) = maximalIdeal R := by
  haveI := h.noeth
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cu_le h)) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun r hr => ?_
  obtain ⟨c, hc⟩ := h.dense 2 r
  have h1 : algebraMap C R c ∈ maximalIdeal R := by
    have := sub_mem hr (Ideal.pow_le_self two_ne_zero hc)
    simpa using this
  have h2 : c ∈ x := by
    have := h.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← this]; exact h1
  have h3 : r = algebraMap C R c + (r - algebraMap C R c) := by ring
  rw [h3]
  refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h2) ?_
  rw [smul_eq_mul, ← pow_two]
  exact hc

private theorem cu_equiv {C R S : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R]
    [CommRing S] [Algebra C S] [IsLocalRing S] {x : Ideal C}
    (h : IsCplAt x R) (h' : IsCplAt x S) : Nonempty (R ≃ₐ[C] S) := by
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨F, hF1, hF2⟩ := cu_ex h (maximalIdeal S) (algebraMap C S) (cu_le h')
  obtain ⟨G, hG1, hG2⟩ := cu_ex h' (maximalIdeal R) (algebraMap C R) (cu_le h)
  have e1 : G.comp F = RingHom.id R :=
    cu_uniq h (maximalIdeal R) _ _ (by rw [RingHom.comp_assoc, hF1, hG1, RingHom.id_comp])
      (fun r hr => hG2 (hF2 hr)) (fun r hr => hr)
  have e2 : F.comp G = RingHom.id S :=
    cu_uniq h' (maximalIdeal S) _ _ (by rw [RingHom.comp_assoc, hG1, hF1, RingHom.id_comp])
      (fun r hr => hF2 (hG2 hr)) (fun r hr => hr)
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G e2 e1) fun c => RingHom.congr_fun hF1 c⟩

theorem UpperTheory.V.CA.cpl_uniq :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ (T : Type) [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T), x ≤ J.comap f → ∃! F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F) ∧ Nonempty (R ≃ₐ[C] Cpl x) ∧ x.map (algebraMap C R) = maximalIdeal R := by
  intro C R _ _ _ _ _ x _ h
  refine ⟨fun T _ J _ f hf => ?_, ?_, cu_map h⟩
  · obtain ⟨F, hF⟩ := cu_ex h J f hf
    exact ⟨F, hF, fun G hG => cu_uniq h J G F (hG.1.trans hF.1.symm) hG.2 hF.2⟩
  · obtain ⟨_, h'⟩ := cpl_is C x
    exact cu_equiv h h'
