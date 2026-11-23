import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ProkerPL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ t ∈ Ine (F := k) B, g⁻¹ * t * g ∈ Ine (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have hm : ∀ x, g x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hv : ∀ x, B.valuation (g x) < 1 ↔ A.valuation x < 1 := fun x => by
    rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hm, ← map_inv₀, hm,
      map_eq_zero_iff _ g.injective]
  refine ⟨g, fun t ht => ⟨?_, fun x hx => ?_⟩⟩
  · show (g⁻¹ * t * g) • A = A
    have h1 : t • B = B := ht.1
    rw [mul_smul, mul_smul, hg, h1, ← hg, inv_smul_smul]
  · rw [← hv, map_sub]
    have e : g ((g⁻¹ * t * g) x) = t (g x) := mul_inv_apply _
    rw [e]
    exact ht.2 _ ((B.valuation_le_one_iff _).2 ((hm x).2 ((A.valuation_le_one_iff _).1 hx)))

open scoped Pointwise in
private theorem res_ine {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (g : G L Ω) : resP L Ω g ∈ Ine (F := Lp L) A ↔ g ∈ Ine (F := L) A := Iff.rfl

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (HeightOneSpectrum (𝓞 k))} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem PL_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) : (PL l H).Normal := by
  refine ⟨fun x hx g => ?_⟩
  unfold PL at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro U hU
  exact U.isNormal'.conj_mem _ (hx U hU) g

theorem UpperTheory.V.Pa.kerLe :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (h : (globOf r V).Hom (globOf r V0)) (H : Subgroup (globOf r V0).Γ) (q : ℕ) (v : Fin q → Plc (Lp L)) (B : Fin q → ValuationSubring Ω) (τ : Fin q → G L Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → V.S' = V0.S' ∪ Set.range v → (∀ j, v j ∉ V0.S' ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ GlobalTheory.TameQuot.IsProGen L (B j) l (τ j)) → (∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1) ∧ (∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l, ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p)) ∧ h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ)) ⊔ PL l (H.comap h.p)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ n r h H q v B τ hp hS hj
  have h1 : ∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1 := fun j g hg =>
    (hp (resP L Ω g)).trans (ine_NS (hj j).1 (hj j).2.1 ((res_ine _ _).2 hg))
  let π : G (Lp L) Ω →* (globOf r V).Γ := toGS Ω V.S'
  have hπ : Continuous π := continuous_toGS Ω V.S'
  have h2 : ∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l,
      ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p) := by
    rintro j _ ⟨g, hg, rfl⟩
    refine prokerPL l (globOf r V).Γ (Ine (F := L) (B j))
      (π.comp ((resP L Ω).comp (Ine (F := L) (B j)).subtype)) (H.comap h.p)
      (hπ.comp (continuous_resP.comp continuous_subtype_val)) (fun x => ?_) g hg
    have : h.p (π (resP L Ω x)) = 1 := h1 j x x.2
    show h.p (π (resP L Ω x)) ∈ H
    rw [this]
    exact H.one_mem
  refine ⟨h1, h2, ?_⟩
  haveI := PL_normal l (H.comap h.p)
  set N : Subgroup (globOf r V).Γ := Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ))
    ⊔ PL l (H.comap h.p) with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  haveI hK : N.topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hc : IsClosed ((N.topologicalClosure.comap π : Subgroup (G (Lp L) Ω)) : Set (G (Lp L) Ω)) :=
    (Subgroup.isClosed_topologicalClosure N).preimage hπ
  have h3 : ∀ j, ∀ g ∈ Ine (F := L) (B j), π (resP L Ω g) ∈ N.topologicalClosure := fun j g hg => by
    have hc' : IsClosed (((N.topologicalClosure.comap π).comap (resP L Ω) : Subgroup (G L Ω)) : Set (G L Ω)) :=
      hc.preimage continuous_resP
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hc' ((hj j).2.2.2.2 hg)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.le_topologicalClosure N
        ((le_sup_left : _ ≤ N) (Subgroup.subset_normalClosure ⟨j, rfl⟩))
    · intro x hx
      exact Subgroup.le_topologicalClosure N ((le_sup_right : _ ≤ N) (h2 j x hx))
  have h4 : NS Ω V0.S' ≤ N.topologicalClosure.comap π := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨u, hu, A, hA, ht⟩ := ht
    by_cases hu' : u ∈ V.S'
    · rw [hS] at hu'
      obtain ⟨j, rfl⟩ := hu'.resolve_left hu
      obtain ⟨g, hg⟩ := conj_ine (hj j).2.1 hA
      have h5 := hg t ht
      obtain ⟨x, hx⟩ := (hj j).2.2.1 (Ine_le_Dec _ h5)
      have h6 : g⁻¹ * t * g ∈ N.topologicalClosure.comap π := by
        rw [← hx] at h5 ⊢
        exact h3 j x ((res_ine _ _).1 h5)
      have h7 := (hK.comap π).conj_mem _ h6 g
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at h7
    · have : π t = 1 := ine_NS hu' hA ht
      show π t ∈ N.topologicalClosure
      rw [this]
      exact one_mem _
  intro x hx
  obtain ⟨g, rfl⟩ : ∃ g, π g = x := QuotientGroup.mk_surjective x
  have h8 : toGS Ω V0.S' g = 1 := (hp g).symm.trans hx
  exact h4 ((QuotientGroup.eq_one_iff g).1 h8)
