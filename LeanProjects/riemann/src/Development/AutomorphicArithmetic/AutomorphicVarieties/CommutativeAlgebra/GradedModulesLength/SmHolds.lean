import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem sm_smith {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] [Module.Finite O P] [Module.IsTorsionFree O P] {r : ℕ} (hr : Module.finrank O P = r)
    (N : Submodule O P) (hN : Module.finrank O N = Module.finrank O P) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (y : Fin r → P) (c : Fin r → ℕ), Submodule.span O (Set.range fun i => ϖ ^ c i • y i) = N ∧
      Module.length O (P ⧸ N) = ((∑ i, c i : ℕ) : ℕ∞) := by
  classical
  let b := Module.finBasisOfFinrankEq O P hr
  have ha := fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Submodule.smithNormalFormCoeffs_ne_zero b hN i) hϖ
  choose c u hu using ha
  refine ⟨fun i => (u i : O) • Submodule.smithNormalFormTopBasis b hN i, c, ?_, ?_⟩
  · have h1 : (fun i => ϖ ^ c i • (u i : O) • Submodule.smithNormalFormTopBasis b hN i) =
        N.subtype ∘ Submodule.smithNormalFormBotBasis b hN := by
      funext i
      simp only [Function.comp, Submodule.subtype_apply]
      rw [Submodule.smithNormalFormBotBasis_def, hu i, smul_smul, mul_comm]
    rw [h1, Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rw [(N.quotientEquivPiSpan b hN).length_eq, Module.length_pi_of_fintype, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Ideal.span {Submodule.smithNormalFormCoeffs b hN i} = maximalIdeal O ^ c i := by
      rw [hu i, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit (u i).isUnit]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

private theorem sm_lift {O P : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup P]
    [Module O P] {r : ℕ} (φ : (Fin (r + 1) → O) →ₗ[O] P) (hr : Module.finrank O (LinearMap.range φ) = r)
    (n : Fin r → P) (hn : Submodule.span O (Set.range n) = LinearMap.range φ) :
    ∃ v : Fin (r + 1) → (Fin (r + 1) → O), Submodule.span O (Set.range v) = ⊤ ∧
      (∀ i : Fin r, φ (v i.castSucc) = n i) ∧ φ (v (Fin.last r)) = 0 := by
  have hw : ∀ i, ∃ w, φ w = n i := fun i => by
    have : n i ∈ LinearMap.range φ := hn ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this
  choose w hw using hw
  have hk : Module.finrank O (LinearMap.ker φ) = 1 := by
    have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
    rw [φ.quotKerEquivRange.finrank_eq, hr, Module.finrank_fin_fun] at h1
    omega
  let b := Module.finBasisOfFinrankEq O (LinearMap.ker φ) hk
  refine ⟨Fin.snoc (α := fun _ => Fin (r + 1) → O) w (b 0 : Fin (r + 1) → O), ?_, fun i => by simp [hw], by simp⟩
  rw [eq_top_iff]
  intro u _
  have h1 : φ u ∈ Submodule.span O (Set.range n) := hn ▸ LinearMap.mem_range_self φ u
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
  have h2 : u - ∑ i, a i • w i ∈ LinearMap.ker φ := by
    simp [LinearMap.mem_ker, map_sum, hw, ha]
  have h3 := congrArg Subtype.val (b.sum_repr ⟨_, h2⟩)
  simp only [Fin.sum_univ_one, Submodule.coe_smul] at h3
  rw [← sub_add_cancel u (∑ i, a i • w i), ← h3]
  refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, by simp⟩)) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)

theorem UpperTheory.V.Alg.M.sm_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [CommRing A] [Algebra O A]
      (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O), (∀ f ∈ 𝒜 (-1), x f = 0) → ∀ (r : ℕ) (F : Fin (r + 1) → A), (∀ i, F i ∈ 𝒜 (-1)) →
      Module.Finite O (cotLat x 𝒜 (-1)) → Module.finrank O (cotLat x 𝒜 (-1)) = r → SpansCot x 𝒜 (-1) F →
      ∀ ϖ : O, Irreducible ϖ → ∃ (F' : Fin (r + 1) → A) (y : Fin r → A) (c : Fin r → ℕ),
        Submodule.span O (Set.range F') = Submodule.span O (Set.range F) ∧
        (∀ i, y i ∈ 𝒜 (-1) ∧ F' i.castSucc - ϖ ^ c i • y i ∈ satSq x) ∧ F' (Fin.last r) ∈ satSq x ∧
        cotLen x 𝒜 (-1) F = ((∑ i, c i : ℕ) : ℕ∞) := by
  intro O _ _ _ A _ _ 𝒜 x hx r F hF hfin hr hs ϖ hϖ
  classical
  haveI : Module.IsTorsionFree O (A ⧸ satSq x) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c p h => ?_
    obtain ⟨f, rfl⟩ := (satSq x).mkQ_surjective p
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨d, hd, h⟩ := h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have hle : cotSpan x F ≤ cotLat x 𝒜 (-1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨F i, ⟨hF i, hx _ (hF i)⟩, rfl⟩
  set N := (cotSpan x F).comap (cotLat x 𝒜 (-1)).subtype with hNdef
  have hN : Module.finrank O N = Module.finrank O (cotLat x 𝒜 (-1)) := by
    have h1 := N.finrank_quotient_add_finrank
    have h2 : Module.finrank O (cotLat x 𝒜 (-1) ⧸ N) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨p, rfl⟩ := N.mkQ_surjective q
      obtain ⟨c, hc, hp⟩ := hs p.1 p.2
      refine ⟨c, hc, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp
    omega
  obtain ⟨y, c, hy, hlen⟩ := sm_smith hr N hN ϖ hϖ
  let ψ : (Fin (r + 1) → O) →ₗ[O] A := Fintype.linearCombination O F
  have hψ : LinearMap.range ψ = Submodule.span O (Set.range F) := Fintype.range_linearCombination O F
  have hφ : LinearMap.range ((satSq x).mkQ ∘ₗ ψ) = cotSpan x F := by
    rw [LinearMap.range_comp, hψ, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmap : N.map (cotLat x 𝒜 (-1)).subtype = cotSpan x F := by
    rw [hNdef, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  obtain ⟨v, hv, hv1, hv2⟩ := sm_lift ((satSq x).mkQ ∘ₗ ψ)
    (by rw [hφ]; exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm.trans (hN.trans hr))
    (fun i => ϖ ^ c i • (y i : A ⧸ satSq x))
    (by rw [hφ, ← hmap, ← hy, Submodule.map_span, ← Set.range_comp]; rfl)
  have hz : ∀ i, ∃ z ∈ 𝒜 (-1), (satSq x).mkQ z = y i := fun i => by
    obtain ⟨z, hz, h⟩ := (y i).2
    exact ⟨z, hz.1, h⟩
  choose z hz hz' using hz
  refine ⟨ψ ∘ v, z, c, ?_, fun i => ⟨hz i, ?_⟩, ?_, hlen⟩
  · rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, hψ]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hz', sub_eq_zero]
    exact hv1 i
  · rw [← Submodule.Quotient.mk_eq_zero]
    exact hv2
