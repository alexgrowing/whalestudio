import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem sep_of_integer {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hs : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
  have h0 : aeval c (minpoly ℤ (c : F)) = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_zero, ← aeval_algebraMap_apply]
    exact minpoly.aeval ℤ (c : F)
  refine ⟨(minpoly ℤ (c : F)).map (algebraMap ℤ ℂ), ?_, ?_⟩
  · have h1 : (minpoly ℤ (c : F)).map (algebraMap ℤ ℂ) = (minpoly ℚ (c : F)).map (algebraMap ℚ ℂ) := by
      rw [hq, Polynomial.map_map]
      congr 1
    rw [h1]
    exact hs.map
  · rw [aeval_map_algebraMap]
    have h2 := aeval_algHom_apply f.toIntAlgHom c (minpoly ℤ (c : F))
    rw [h0, map_zero] at h2
    exact h2

private theorem exDiag (hSim : SimDiag) (hExt : ExtendEmb) {F : Type} [Field F] [NumberField F]
    {O : Type} [Ring O] {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) :
    ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)), IsDiag a ρ 1 Sb ty 1 := by
  obtain ⟨Sb, d, hdet, hd⟩ := hSim g (𝓞 F) (fun c => ρ (a c))
    (fun c c' => by
      show ρ (a c) * ρ (a c') = ρ (a c') * ρ (a c)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm])
    (fun c => sep_of_integer (ρ.comp a) c)
  have hunit : IsUnit Sb.det := isUnit_iff_ne_zero.2 hdet
  have hdiag : ∀ c : 𝓞 F, Matrix.diagonal (d c) = Sb⁻¹ * ρ (a c) * Sb := by
    intro c
    rw [Matrix.mul_assoc, hd c, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  have hent : ∀ c i, d c i = (Sb⁻¹ * ρ (a c) * Sb) i i := by
    intro c i
    rw [← hdiag, Matrix.diagonal_apply_eq]
  have hmul : ∀ c c' i, d (c * c') i = d c i * d c' i := by
    intro c c' i
    have h1 : Matrix.diagonal (d (c * c')) = Matrix.diagonal (d c) * Matrix.diagonal (d c') := by
      rw [hdiag, hdiag, hdiag, map_mul, map_mul]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hunit]
    rw [Matrix.diagonal_mul_diagonal] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  let f : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => d c i
      map_one' := by
        rw [hent, map_one, map_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]
      map_mul' := fun c c' => hmul c c' i
      map_zero' := by
        rw [hent, map_zero, map_zero]
        simp
      map_add' := fun c c' => by
        rw [hent, hent, hent, map_add, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] }
  choose ty hty using fun i => hExt F (f i)
  refine ⟨Sb, ty, hdet, fun c => ?_, ?_⟩
  · have h1 : (fun i => ty i (c : F)) = d c := funext fun i => (hty i c).symm
    rw [h1]
    exact hd c
  · rw [Matrix.one_mul]
    have : Matrix.diagonal (1 : Fin g → ℂ) = 1 := Matrix.diagonal_one
    rw [this, Matrix.mul_one]

private theorem exR {g : ℕ} {Idx : Type} (E : Fin g ≃ Idx) (s : Idx → Prop)
    (Sb : Matrix (Fin g) (Fin g) ℂ) (hdet : Sb.det ≠ 0) :
    ∃ R : (Idx → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, R x =
      Sb *ᵥ (fun j => if s (E j) then x (E j) else (starRingEnd ℂ) (x (E j))) := by
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨{ toFun := fun x => Sb *ᵥ (fun j => if s (E j) then x (E j) else (starRingEnd ℂ) (x (E j)))
            map_add' := ?_
            map_smul' := ?_
            invFun := fun y k => if s k then (Sb⁻¹ *ᵥ y) (E.symm k) else (starRingEnd ℂ) ((Sb⁻¹ *ᵥ y) (E.symm k))
            left_inv := ?_
            right_inv := ?_ }, fun x => rfl⟩
  · intro x y
    rw [← Matrix.mulVec_add]
    congr 1
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  · intro t x
    simp only [RingHom.id_apply]
    rw [← Matrix.mulVec_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply]
    split_ifs <;> simp [Complex.real_smul]
  · intro x
    funext k
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Equiv.apply_symm_apply]
    split_ifs <;> simp
  · intro y
    have h : (fun j => if s (E j) then (if s (E j) then (Sb⁻¹ *ᵥ y) (E.symm (E j)) else (starRingEnd ℂ) ((Sb⁻¹ *ᵥ y) (E.symm (E j))))
        else (starRingEnd ℂ) (if s (E j) then (Sb⁻¹ *ᵥ y) (E.symm (E j)) else (starRingEnd ℂ) ((Sb⁻¹ *ᵥ y) (E.symm (E j))))) = Sb⁻¹ *ᵥ y := by
      funext j
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> simp
    show Sb *ᵥ _ = y
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

private theorem rootsW {p : ℕ} [Fact p.Prime] (D : Datum p) (hne : (starRingEnd ℂ) D.ρc ≠ D.ρc) (τ : D.F →+* ℂ) :
    τ (D.ω : D.F) = D.ρc ∨ τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
  have h0 : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have h2 : τ (D.ω : D.F) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have h := congrArg (fun c : 𝓞 D.F => τ (c : D.F)) h0
    simpa using h
  have h3 := D.ρc_root
  have h4 : (starRingEnd ℂ) D.ρc ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have h := congrArg (starRingEnd ℂ) h3
    simpa using h
  have ht : (D.tr : ℂ) - (D.ρc + (starRingEnd ℂ) D.ρc) = 0 := by
    have h : (D.ρc - (starRingEnd ℂ) D.ρc) * ((D.tr : ℂ) - (D.ρc + (starRingEnd ℂ) D.ρc)) = 0 := by
      linear_combination h4 - h3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
  have h5 : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    linear_combination h2 - h3 + (τ (D.ω : D.F) - D.ρc) * ht
  rcases mul_eq_zero.1 h5 with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

section Count

variable {F F' : Type} [Field F] [Field F'] [NumberField F] [NumberField F'] (e : F ≃+* F') (w : F) (r : ℂ)
  (v : InfinitePlace F') {n : ℕ} (i₀ : Fin n)

private def sS (idx : InfinitePlace F' × Fin n) : Prop := idx = (v, i₀) ↔ idx.1.embedding (e w) = r

private noncomputable def ty0 (idx : InfinitePlace F' × Fin n) : F →+* ℂ :=
  if sS e w r v i₀ idx then idx.1.embedding.comp (e : F →+* F')
  else ComplexEmbedding.conjugate (idx.1.embedding.comp (e : F →+* F'))

private theorem cmType_apply_positive {idx : InfinitePlace F' × Fin n} (h : sS e w r v i₀ idx) (x : F) :
    ty0 e w r v i₀ idx x = idx.1.embedding (e x) := by
  rw [ty0, if_pos h]
  rfl

private theorem cmType_apply_negative {idx : InfinitePlace F' × Fin n} (h : ¬ sS e w r v i₀ idx) (x : F) :
    ty0 e w r v i₀ idx x = (starRingEnd ℂ) (idx.1.embedding (e x)) := by
  rw [ty0, if_neg h]
  rfl

private theorem cmType_infinitePlace (idx : InfinitePlace F' × Fin n) :
    InfinitePlace.mk ((ty0 e w r v i₀ idx).comp (e.symm : F' →+* F)) = idx.1 := by
  by_cases h : sS e w r v i₀ idx
  · have h1 : (ty0 e w r v i₀ idx).comp (e.symm : F' →+* F) = idx.1.embedding := by
      ext x
      simp [cmType_apply_positive e w r v i₀ h]
    rw [h1, InfinitePlace.mk_embedding]
  · have h1 : (ty0 e w r v i₀ idx).comp (e.symm : F' →+* F) = ComplexEmbedding.conjugate idx.1.embedding := by
      ext x
      simp [cmType_apply_negative e w r v i₀ h, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem cmType_at_place_iff (hr : ∀ τ : F →+* ℂ, τ w = r ∨ τ w = (starRingEnd ℂ) r) (hne : (starRingEnd ℂ) r ≠ r)
    (idx : InfinitePlace F' × Fin n) : ty0 e w r v i₀ idx w = r ↔ idx = (v, i₀) := by
  by_cases h : sS e w r v i₀ idx
  · rw [cmType_apply_positive e w r v i₀ h]
    exact h.symm
  · rw [cmType_apply_negative e w r v i₀ h]
    have hc : idx.1.embedding (e w) = r ∨ idx.1.embedding (e w) = (starRingEnd ℂ) r :=
      hr (idx.1.embedding.comp (e : F →+* F'))
    rcases hc with hc | hc
    · have h1 : idx ≠ (v, i₀) := fun h2 => h ⟨fun _ => hc, fun _ => h2⟩
      rw [hc]
      exact ⟨fun h2 => absurd h2 hne, fun h2 => absurd h2 h1⟩
    · have h1 : idx.1.embedding (e w) ≠ r := by
        rw [hc]
        exact hne
      have h2 : idx = (v, i₀) := by
        by_contra h3
        exact h ⟨fun h4 => absurd h4 h3, fun h4 => absurd h4 h1⟩
      rw [hc]
      simp [h2]

private theorem emb_sep (hr : ∀ τ : F →+* ℂ, τ w = r ∨ τ w = (starRingEnd ℂ) r) (hne : (starRingEnd ℂ) r ≠ r)
    (τ τ' : F →+* ℂ) (hm : InfinitePlace.mk (τ.comp (e.symm : F' →+* F)) = InfinitePlace.mk (τ'.comp (e.symm : F' →+* F)))
    (hw : τ w = τ' w) : τ = τ' := by
  rcases InfinitePlace.mk_eq_iff.1 hm with h | h
  · ext x
    have h1 := RingHom.congr_fun h (e x)
    simpa using h1
  · exfalso
    have h1 := RingHom.congr_fun h (e w)
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h1
    rw [← hw] at h1
    rcases hr τ with h2 | h2
    · rw [h2] at h1
      exact hne h1
    · rw [h2] at h1
      simp only [Complex.conj_conj] at h1
      exact hne h1.symm

private theorem cmType_card_fiber (t₀ : F →+* ℂ) (hr : ∀ τ : F →+* ℂ, τ w = r ∨ τ w = (starRingEnd ℂ) r)
    (hne : (starRingEnd ℂ) r ≠ r) (ht : t₀ w = r)
    (hb : (∀ x, v.embedding (e x) = t₀ x) ∨ (∀ x, (starRingEnd ℂ) (v.embedding (e x)) = t₀ x)) (τ : F →+* ℂ) :
    Fintype.card {idx // ty0 e w r v i₀ idx = τ} = typeMult n t₀ (fun τ => if τ w = r then 0 else 1) τ := by
  have hB : ty0 e w r v i₀ (v, i₀) = t₀ := by
    rcases hb with hb | hb
    · have h1 : v.embedding (e w) = r := by rw [hb, ht]
      have h2 : sS e w r v i₀ (v, i₀) := ⟨fun _ => h1, fun _ => rfl⟩
      ext x
      rw [cmType_apply_positive e w r v i₀ h2]
      exact hb x
    · have h1 : v.embedding (e w) ≠ r := by
        intro h
        have h3 := hb w
        rw [h, ht] at h3
        exact hne h3
      have h2 : ¬ sS e w r v i₀ (v, i₀) := fun h => h1 (h.1 rfl)
      ext x
      rw [cmType_apply_negative e w r v i₀ h2]
      exact hb x
  have hconj : (ComplexEmbedding.conjugate t₀) w = (starRingEnd ℂ) r := by
    rw [ComplexEmbedding.conjugate_coe_eq, ht]
  have hcne : ComplexEmbedding.conjugate t₀ ≠ t₀ := by
    intro h
    rw [h, ht] at hconj
    exact hne hconj.symm
  rw [Fintype.card_subtype]
  by_cases hτ : τ w = r
  · by_cases h0 : τ = t₀
    · have hf : (Finset.univ.filter fun idx => ty0 e w r v i₀ idx = τ) = {(v, i₀)} := by
        ext idx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          exact (cmType_at_place_iff e w r v i₀ hr hne idx).1 (by rw [h, hτ])
        · rintro rfl
          rw [hB, h0]
      rw [hf, typeMult, if_pos h0, Finset.card_singleton]
    · have hf : (Finset.univ.filter fun idx => ty0 e w r v i₀ idx = τ) = ∅ := by
        ext idx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h
        have h1 := (cmType_at_place_iff e w r v i₀ hr hne idx).1 (by rw [h, hτ])
        rw [h1, hB] at h
        exact h0 h.symm
      have h1 : τ ≠ ComplexEmbedding.conjugate t₀ := by
        intro h
        rw [h, hconj] at hτ
        exact hne hτ
      rw [hf, typeMult, if_neg h0, if_neg h1, if_pos hτ]
      simp
  · have hτ' : τ w = (starRingEnd ℂ) r := (hr τ).resolve_left hτ
    have h0 : τ ≠ t₀ := fun h => hτ (by rw [h, ht])
    have hf : (Finset.univ.filter fun idx => ty0 e w r v i₀ idx = τ) =
        (({InfinitePlace.mk (τ.comp (e.symm : F' →+* F))} : Finset _) ×ˢ (Finset.univ : Finset (Fin n))).erase (v, i₀) := by
      ext idx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, Finset.mem_product,
        Finset.mem_singleton, and_true]
      constructor
      · intro h
        refine ⟨fun h1 => ?_, ?_⟩
        · have h2 := (cmType_at_place_iff e w r v i₀ hr hne idx).2 h1
          rw [h] at h2
          exact hτ h2
        · rw [← h]
          exact (cmType_infinitePlace e w r v i₀ idx).symm
      · rintro ⟨h1, h2⟩
        refine emb_sep e w r hr hne _ _ ?_ ?_
        · rw [cmType_infinitePlace e w r v i₀ idx]
          exact h2
        · rw [hτ']
          exact (hr _).resolve_left fun h => h1 ((cmType_at_place_iff e w r v i₀ hr hne idx).1 h)
    have hpl : InfinitePlace.mk (t₀.comp (e.symm : F' →+* F)) = v := by
      have h1 := cmType_infinitePlace e w r v i₀ (v, i₀)
      rwa [hB] at h1
    have hpc : InfinitePlace.mk ((ComplexEmbedding.conjugate t₀).comp (e.symm : F' →+* F)) = v := by
      have h1 : (ComplexEmbedding.conjugate t₀).comp (e.symm : F' →+* F) =
          ComplexEmbedding.conjugate (t₀.comp (e.symm : F' →+* F)) := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [h1, InfinitePlace.mk_conjugate_eq, hpl]
    rw [hf]
    by_cases h1 : τ = ComplexEmbedding.conjugate t₀
    · have h2 : InfinitePlace.mk (τ.comp (e.symm : F' →+* F)) = v := by rw [h1, hpc]
      rw [typeMult, if_neg h0, if_pos h1, h2, Finset.card_erase_of_mem (by simp)]
      simp
    · have h2 : InfinitePlace.mk (τ.comp (e.symm : F' →+* F)) ≠ v := by
        intro h
        exact h1 (emb_sep e w r hr hne _ _ (by rw [h, hpc]) (by rw [hτ', hconj]))
      rw [typeMult, if_neg h0, if_neg h1, if_neg hτ, Finset.erase_eq_of_notMem (by simp [h2])]
      simp

end Count

theorem UpperTheory.Gal.W2.typeIso_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.PlaceT → UpperTheory.Gal.W2.TypeIso := by
  intro hSim hExt hCount hPlace p _ D G L ha v hv t₀ htau ρ hsig i₀
  obtain ⟨-, hω, hne, hb⟩ := hPlace p D G L ha v hv t₀ htau
  obtain ⟨Sb, ty, hD⟩ := exDiag hSim hExt ρ (algebraMap (𝓞 D.F) D.O)
  have hr := rootsW D hne
  have hb' : (∀ x, v.embedding (L.e x) = t₀ x) ∨ (∀ x, (starRingEnd ℂ) (v.embedding (L.e x)) = t₀ x) := by
    rcases hb with ⟨-, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hcnt : ∀ τ, Fintype.card {j // ty j = τ} = typeMult D.n t₀ (epsD D) τ := by
    intro τ
    have h := (hCount D.F D.O D.inv D.g ρ (algebraMap _ _) D.n t₀ (epsD D) hsig 1 Sb ty 1 hD τ).1
    rw [← h, evAt, Multiset.card_map, Fintype.card_subtype]
    rfl
  have hcnt2 : ∀ τ, Fintype.card {idx // ty0 L.e (D.ω : D.F) D.ρc v i₀ idx = τ} = typeMult D.n t₀ (epsD D) τ := by
    intro τ
    have h := cmType_card_fiber L.e (D.ω : D.F) D.ρc v i₀ t₀ hr hne hω hb' τ
    exact h.trans (congrArg (fun m => typeMult m t₀ (epsD D) τ) L.n_eq)
  let E : Fin D.g ≃ (InfinitePlace G.F × Fin G.n) := Equiv.ofFiberEquiv (f := ty)
    (g := ty0 L.e (D.ω : D.F) D.ρc v i₀) fun τ => Fintype.equivOfCardEq (by rw [hcnt, hcnt2])
  have hE : ∀ j, ty0 L.e (D.ω : D.F) D.ρc v i₀ (E j) = ty j := fun j => Equiv.ofFiberEquiv_map _ j
  obtain ⟨R₁, hR₁⟩ := exR E (sS L.e (D.ω : D.F) D.ρc v i₀) Sb hD.1
  have hR : ∀ x : Arch G, ((LinearEquiv.curry ℝ ℂ (InfinitePlace G.F) (Fin G.n)).symm ≪≫ₗ R₁) x =
      Sb *ᵥ (fun j => if sS L.e (D.ω : D.F) D.ρc v i₀ (E j) then x (E j).1 (E j).2
        else (starRingEnd ℂ) (x (E j).1 (E j).2)) := fun x => hR₁ _
  have hsign : ∀ idx : InfinitePlace G.F × Fin G.n,
      (if idx.1 = v ∧ idx.2 = i₀ then (1 : ℂ) else -1) * (sgnV L idx.1 * Complex.I) =
        if sS L.e (D.ω : D.F) D.ρc v i₀ idx then Complex.I else -Complex.I := by
    rintro ⟨v', i⟩
    by_cases h1 : v' = v ∧ i = i₀ <;> by_cases h2 : v'.embedding (L.e (D.ω : D.F)) = D.ρc
    · have h3 : sS L.e (D.ω : D.F) D.ρc v i₀ (v', i) := ⟨fun _ => h2, fun _ => by rw [h1.1, h1.2]⟩
      rw [if_pos h3, if_pos h1, sgnV, if_pos h2]
      ring
    · have h3 : ¬ sS L.e (D.ω : D.F) D.ρc v i₀ (v', i) := fun h => h2 (h.1 (by rw [h1.1, h1.2]))
      rw [if_neg h3, if_pos h1, sgnV, if_neg h2]
      ring
    · have h3 : ¬ sS L.e (D.ω : D.F) D.ρc v i₀ (v', i) := fun h => h1 (by simpa using h.2 h2)
      rw [if_neg h3, if_neg h1, sgnV, if_pos h2]
      ring
    · have h3 : sS L.e (D.ω : D.F) D.ρc v i₀ (v', i) :=
        ⟨fun h => absurd (by simpa using h) h1, fun h => absurd h h2⟩
      rw [if_pos h3, if_neg h1, sgnV, if_neg h2]
      ring
  refine ⟨(LinearEquiv.curry ℝ ℂ (InfinitePlace G.F) (Fin G.n)).symm ≪≫ₗ R₁, fun x => ?_, fun c x => ?_⟩
  · rw [hR, hR, ← Matrix.mulVec_smul]
    congr 1
    funext j
    have h := hsign (E j)
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hs : sS L.e (D.ω : D.F) D.ρc v i₀ (E j)
    · rw [if_pos hs] at h
      rw [if_pos hs, if_pos hs, h]
    · rw [if_neg hs] at h
      rw [if_neg hs, if_neg hs, h]
      simp
  · rw [hR, hR, Matrix.mulVec_mulVec, hD.2.1 c, ← Matrix.mulVec_mulVec]
    congr 1
    funext j
    rw [Matrix.mulVec_diagonal, ← hE j]
    by_cases hs : sS L.e (D.ω : D.F) D.ρc v i₀ (E j)
    · rw [if_pos hs, if_pos hs, cmType_apply_positive L.e _ _ v i₀ hs]
      simp
    · rw [if_neg hs, if_neg hs, cmType_apply_negative L.e _ _ v i₀ hs]
      simp
