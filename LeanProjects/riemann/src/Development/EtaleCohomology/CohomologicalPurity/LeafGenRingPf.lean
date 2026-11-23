import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section

namespace LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity

theorem inj_sq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) (y : A)
    (hy : φ y ∈ (I ^ 2).map φ) : y ∈ I ^ 2 := by
  let _ := φ.toAlgebra
  have _ : Algebra.Etale A B := h.1
  let e := RingEquiv.ofBijective _ h.2
  let f : B →ₐ[A] A ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))
      commutes' := fun a => by
        change e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk I a
        rw [e.symm_apply_eq]
        rfl }
  let g : A ⧸ I ^ 2 →ₐ[A] A ⧸ I := Ideal.Quotient.factorₐ A (Ideal.pow_le_self two_ne_zero)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)
  have hn : IsNilpotent (RingHom.ker (g : A ⧸ I ^ 2 →+* A ⧸ I)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, ← le_bot_iff]
    refine le_trans (le_of_eq (pow_two _)) ?_
    refine Ideal.mul_le.mpr fun x hx z hz => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hz' : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hx' hz'
  let σ := Algebra.FormallySmooth.liftOfSurjective f g hg hn
  have hσ : ∀ a, σ (φ a) = Ideal.Quotient.mk (I ^ 2) a := fun a => σ.commutes a
  have hc : (σ : B →+* A ⧸ I ^ 2).comp φ = Ideal.Quotient.mk (I ^ 2) := RingHom.ext hσ
  have h0 := Ideal.mem_map_of_mem (σ : B →+* A ⧸ I ^ 2) hy
  rw [Ideal.map_map, hc, Ideal.map_quotient_self, Ideal.mem_bot] at h0
  change σ (φ y) = 0 at h0
  rw [hσ] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem approx {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ) (J : Ideal A) (T : Set B)
    (hT : ∀ t ∈ T, t ∈ I.map φ ∧ ∃ c ∈ J, t - φ c ∈ I.map φ ^ 2) :
    ∀ z ∈ Ideal.span T, ∃ c ∈ J, z - φ c ∈ I.map φ ^ 2 := by
  have hle : Ideal.span T ≤ I.map φ := Ideal.span_le.mpr fun t ht => (hT t ht).1
  intro z hz
  induction hz using Submodule.span_induction with
  | mem t ht => exact (hT t ht).2
  | zero => exact ⟨0, J.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨c, hc, hxc⟩ := ihx
    obtain ⟨c', hc', hyc⟩ := ihy
    refine ⟨c + c', J.add_mem hc hc', ?_⟩
    have : x + y - φ (c + c') = (x - φ c) + (y - φ c') := by rw [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hxc hyc
  | smul b x hx ih =>
    obtain ⟨c, hc, hxc⟩ := ih
    obtain ⟨c', hbc⟩ := hs b
    refine ⟨c' * c, J.mul_mem_left _ hc, ?_⟩
    have : b • x - φ (c' * c) = (b - φ c') * x + φ c' * (x - φ c) := by
      rw [map_mul, smul_eq_mul]; ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hxc)
    rw [pow_two]
    exact Ideal.mul_mem_mul hbc (hle hx)

end LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity.GenRingPf in
theorem LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := by
  intro d A _ I hI hC
  obtain ⟨B, _, φ, ψ, hN, _, hspan, _⟩ := hC
  have hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ := by
    intro b
    obtain ⟨x, hx⟩ := hN.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨c, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have := (I.map φ).neg_mem hx
    rwa [neg_sub] at this
  have hI1 : ∀ z ∈ I.map φ, ∃ c ∈ I, z - φ c ∈ I.map φ ^ 2 :=
    approx φ I hs I (φ '' I) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := ht
      exact ⟨Ideal.mem_map_of_mem _ hi, i, hi, by simp⟩)
  have hX : ∀ j, ∃ c ∈ I, ψ (MvPolynomial.X j) - φ c ∈ I.map φ ^ 2 := fun j =>
    hI1 _ (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha hax using hX
  have hle : I ≤ Ideal.span (Set.range a) ⊔ I • I := by
    intro y hy
    have hy' : φ y ∈ Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) := hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc, hyc⟩ := approx φ I hs (Ideal.span (Set.range a)) _ (fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact ⟨hspan ▸ Ideal.subset_span ⟨j, rfl⟩, a j, Ideal.subset_span ⟨j, rfl⟩, hax j⟩) _ hy'
    have h2 : y - c ∈ I ^ 2 := inj_sq φ I hN _ (by rw [map_sub, Ideal.map_pow]; exact hyc)
    have : y = c + (y - c) := by ring
    rw [this]
    refine Submodule.add_mem_sup hc ?_
    rw [Ideal.smul_eq_mul, ← pow_two]; exact h2
  obtain ⟨r, hr, hrle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hI le_rfl hle
  refine ⟨a, r, hr, ha, fun y hy => ?_⟩
  have := hrle (Submodule.smul_mem_pointwise_smul y r I hy)
  simpa [smul_eq_mul] using this
