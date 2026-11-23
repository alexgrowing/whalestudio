import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem rel_pres_min {A ι : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Fintype ι]
    (K K0 : Ideal A) (f : ι → A) (h : K = K0 ⊔ Ideal.span (Set.range f)) :
    ∃ s : Finset ι, K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) ∧
      ∀ c : s → A, ∑ u, c u * f u ∈ K0 ⊔ maximalIdeal A * K → ∀ u, c u ∈ maximalIdeal A := by
  classical
  have hex : ∃ n, ∃ s : Finset ι, s.card = n ∧ K = K0 ⊔ Ideal.span (Set.range fun u : s => f u) := by
    refine ⟨_, Finset.univ, rfl, ?_⟩
    rw [h]
    congr 2
    ext x
    simp
  obtain ⟨s, hs, hK⟩ := Nat.find_spec hex
  refine ⟨s, hK, fun c hc u => ?_⟩
  by_contra hu
  have hun : IsUnit (c u) := by
    by_contra h'
    exact hu h'
  obtain ⟨v, hv⟩ := hun
  refine Nat.find_min hex (m := (s.erase u).card) (by rw [← hs]; exact Finset.card_erase_lt_of_mem u.2)
    ⟨s.erase u, rfl, ?_⟩
  set N : Ideal A := K0 ⊔ Ideal.span (Set.range fun w : s.erase u => f w) with hN
  have hmem : ∀ w : s, w ≠ u → f w ∈ N := fun w hw =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨⟨w, Finset.mem_erase.2 ⟨fun e => hw (Subtype.ext e), w.2⟩⟩, rfl⟩)
  have hNK : N ≤ K := by
    rw [hK]
    refine sup_le_sup_left (Ideal.span_mono ?_) _
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, Finset.mem_of_mem_erase w.2⟩, rfl⟩
  refine le_antisymm ?_ hNK
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) (IsNoetherian.noetherian K)
    (maximalIdeal_le_jacobson _) ?_
  have h1 : f u ∈ N ⊔ maximalIdeal A • K := by
    have h2 : ∑ w, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      (sup_le_sup_right (le_sup_left : K0 ≤ N) (maximalIdeal A * K)) hc
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)] at h2
    have h3 : ∑ w ∈ Finset.univ.erase u, c w * f w ∈ N ⊔ maximalIdeal A • K :=
      Ideal.mem_sup_left (Ideal.sum_mem _ fun w hw =>
        Ideal.mul_mem_left _ _ (hmem w (Finset.mem_erase.1 hw).1))
    have h4 := Ideal.mul_mem_left _ (↑v⁻¹ : A) (sub_mem h2 h3)
    rwa [add_sub_cancel_right, ← hv, Units.inv_mul_cancel_left] at h4
  conv_lhs => rw [hK]
  refine sup_le (le_sup_of_le_left le_sup_left) (Ideal.span_le.2 ?_)
  rintro _ ⟨w, rfl⟩
  by_cases hw : w = u
  · subst hw; exact h1
  · exact Ideal.mem_sup_left (hmem w hw)

private theorem rel_pres_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem rel_pres_max_le {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type}
    [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R) (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span (Set.range W.z) ⊔ (maximalIdeal O).map (algebraMap O R) := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := rel_pres_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : constantCoeff f ∈ maximalIdeal O := fun hu => h3 (hu.map _)
  have h5 := h2 (Ideal.span (Set.range W.z)) fun s => Ideal.subset_span ⟨s, rfl⟩
  simpa using add_mem (Ideal.mem_sup_left h5)
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem (algebraMap O R) h4))

theorem UpperTheory.V.Alg.rel_pres :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (WB : WPres O X B) (W₀ : WPres O X R) (i : B →ₐ[O] R), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ s, W₀.z s ∈ maximalIdeal R) → (∀ s, i (WB.z s) ∈ W₀.part (WB.wt s)) →
      ∀ (τ : Type) [Fintype τ] (z : τ → R) (wt : τ → X), (∀ t, z t ∈ maximalIdeal R ∧ z t ∈ W₀.part (wt t)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∃ (W : WPres O X R) (κ : Type) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → X), IsRelPres WB i W e f wf ∧
        (∀ t, W.z (e (.inr t)) = z t ∧ W.wt (e (.inr t)) = wt t) ∧ (∀ j, W.part j = W₀.part j) ∧
        ∀ c : κ → O, ∑ u, c u • f u ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ⊔ maximalIdeal (MvPowerSeries W.σ O) * RingHom.ker W.π → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ X _ _ _ B _ _ _ R _ _ _ WB W₀ i hB h0 hi τ _ z wt hz hgen
  classical
  have him : ∀ s, i (WB.z s) ∈ maximalIdeal R := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hB s
  have hz' : ∀ s : WB.σ ⊕ τ, Sum.elim (fun s => i (WB.z s)) z s ∈ maximalIdeal R ∧
      Sum.elim (fun s => i (WB.z s)) z s ∈ W₀.part (Sum.elim WB.wt wt s) := by
    rintro (s | t)
    · exact ⟨him s, hi s⟩
    · exact hz t
  obtain ⟨W, e, he⟩ := pres_new O X R W₀ h0 (WB.σ ⊕ τ) (Sum.elim WB.wt wt) (Sum.elim (fun s => i (WB.z s)) z) hz'
    (hgen.trans (sup_le_sup_right (sup_le (le_sup_of_le_left (Ideal.span_mono (by
      rintro _ ⟨t, rfl⟩
      exact ⟨.inr t, rfl⟩))) (by
        refine (Ideal.map_mono (rel_pres_max_le WB hB)).trans ?_
        rw [Ideal.map_sup]
        refine sup_le_sup ?_ ?_
        · rw [Ideal.map_span]
          refine Ideal.span_mono ?_
          rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
          exact ⟨.inl s, rfl⟩
        · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_map_of_mem _ hc)) _))
  have hW : ∀ s, W.z s ∈ maximalIdeal R ∧ W.z s ∈ W₀.part (W.wt s) := fun s => by
    obtain ⟨s, rfl⟩ := e.surjective s
    rw [(he s).1, (he s).2]
    exact hz' s
  have hpart := pres_indep O X R W₀ h0 W (fun s => (hW s).1) fun s => (hW s).2
  have hcomm : W.π.comp (MvPowerSeries.rename fun s => e (.inl s)) = i.comp WB.π := by
    refine (co_ev O O R WB.σ (Algebra.ofId _ _) _ him).unique ⟨fun x => ?_, fun s => ?_⟩ ⟨fun x => ?_, fun s => rfl⟩
    · exact AlgHom.commutes _ x
    · rw [AlgHom.comp_apply, rename_X]
      exact (he (.inl s)).1
    · exact AlgHom.commutes _ x
  have hcomm' : ∀ x, W.π (MvPowerSeries.rename (fun s => e (.inl s)) x) = i (WB.π x) :=
    fun x => AlgHom.congr_fun hcomm x
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  obtain ⟨n, g, c, hg, hK⟩ := ker_gen O X W.σ W.wt _ W.homog
  have hle : (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ≤ RingHom.ker W.π := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm', (RingHom.mem_ker).1 hx, map_zero]
  obtain ⟨s, hs, hmin⟩ := rel_pres_min (RingHom.ker W.π)
    ((RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s))) g (by rw [← hK, sup_eq_right.2 hle])
  refine ⟨W, s, inferInstance, e, fun u => g u, fun u => c u, ⟨fun s => (he (.inl s)).2, hcomm', fun u => hg u, hs⟩,
    fun t => he (.inr t), hpart, fun a ha u hu => ?_⟩
  refine hmin (fun u => algebraMap O _ (a u)) ?_ u (hu.map _)
  simpa only [Algebra.smul_def] using ha
