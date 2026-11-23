import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') {c : C} (hc : c ∈ maximalIdeal C) :
    φ c ∈ maximalIdeal C' := by
  rwa [← res_eq_zero_iff O, res_map φ, res_eq_zero_iff]

private theorem pow_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : φ c ∈ maximalIdeal C' ^ N := by
  have h : (maximalIdeal C).map φ ≤ maximalIdeal C' := Ideal.map_le_iff_le_comap.2 fun _ h => max_map φ h
  have h2 := Ideal.mem_map_of_mem φ hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h N h2

private theorem span_map {C C' K K' : Type} [CommRing C] [CommRing C'] [CommRing K] [CommRing K'] [Algebra C K]
    [Algebra C' K'] (φ : C → C') (f : K →+* K') (h : ∀ c, f (algebraMap C K c) = algebraMap C' K' (φ c))
    {s : Set K} {M : Submodule C' K'} (hs : ∀ x ∈ s, f x ∈ M) {x : K} (hx : x ∈ Submodule.span C s) : f x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]; exact M.smul_mem _ hx

private theorem lc_of {X A B : Type} [TopologicalSpace X] {u : X → A} {v : X → B} (hu : IsLocallyConstant u)
    (h : ∀ x y, u x = u y → v x = v y) : IsLocallyConstant v := by
  rw [IsLocallyConstant.iff_eventually_eq] at hu ⊢
  exact fun x => (hu x).mono fun y hy => h _ _ hy

theorem UpperTheory.V.Fr.frobenius_corner_cone_map :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (K' : Type) [CommRing K'] [Algebra C' K'] (β : C →ₐ[O] C') (f : K →+* K'), (∀ c, f (algebraMap C K c) = algebraMap C' K' (β c)) → ∀ ρ : NRep F n K, Cone O C ρ → Cone O C' (ρ.map f) := by
  intro l _ O _ _ F n C _ _ _ K _ _ C' _ _ _ K' _ _ φ f h ρ H
  have hsp : ∀ i j, ∀ x ∈ Submodule.span C (Set.range fun g => ρ.r g i j),
      f x ∈ Submodule.span C' (Set.range fun g => (ρ.map f).r g i j) := fun i j x hx =>
    span_map φ f h (by rintro _ ⟨g, rfl⟩; exact Submodule.subset_span ⟨g, rfl⟩) hx
  refine ⟨fun g i => ?_, fun L hL hs => ?_, fun i j => ?_, fun i j N => ?_, ?_⟩
  · obtain ⟨c, h1, h2⟩ := H.dg g i
    exact ⟨φ c, by rw [← h, h1, NRep.map_r], by rw [res_map, h2]⟩
  · obtain ⟨c, h1, h2⟩ := H.cyc L hL hs
    refine ⟨φ c, max_map φ h1, ?_⟩
    rw [← h, h2, map_list_prod, List.map_map]
    rfl
  · classical
    obtain ⟨t, ht⟩ := H.fg i j
    refine ⟨t.image f, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact hsp i j x (ht ▸ Submodule.subset_span hx)
    · rintro _ ⟨g, rfl⟩
      refine span_map φ f h (s := (t : Set K)) (fun x hx => Submodule.subset_span ?_) (x := ρ.r g i j) ?_
      · exact Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)
      · rw [ht]; exact Submodule.subset_span ⟨g, rfl⟩
  · refine lc_of (H.cont i j N) fun x y hxy => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hxy ⊢
    rw [NRep.map_r, NRep.map_r, ← map_sub]
    refine Submodule.smul_induction_on hxy (fun a ha z hz => ?_) (fun a b ha hb => ?_)
    · rw [Algebra.smul_def a z, map_mul, h, ← Algebra.smul_def (φ a) (f z)]
      exact Submodule.smul_mem_smul (pow_map φ N ha) (hsp i j z hz)
    · rw [map_add]; exact add_mem ha hb
  · obtain ⟨χ, h1, h2⟩ := H.psi
    refine ⟨fun v i g => φ (χ v i g), fun v i => ⟨fun N => ?_, fun g => ?_⟩, fun v i g => ?_⟩
    · refine lc_of ((h1 v i).1 N) fun x y hxy => ?_
      rw [Ideal.Quotient.eq] at hxy ⊢
      rw [← map_sub]
      exact pow_map φ N hxy
    · rw [res_map, (h1 v i).2]
    · rw [← h, h2, NRep.map_ψ]
