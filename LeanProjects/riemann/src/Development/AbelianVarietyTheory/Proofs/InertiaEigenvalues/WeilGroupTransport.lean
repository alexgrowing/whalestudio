import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped IntermediateField

noncomputable section

theorem GlobalTheory.LocLanglands.exists_isLocalExt_transport : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (c : Weil h ≃* Weil h'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → (∀ σ, WeilRel φ σ (c σ)) → ∀ L : IntermediateField E Ω, FiniteDimensional E L → IsLocalExt L h → ∃ (L' : IntermediateField E' Ω') (jL : L →+* L'), FiniteDimensional E' L' ∧ IsLocalExt L' h' ∧ Module.finrank E' L' = Module.finrank E L ∧ (∀ x : L, φ (x : Ω) = (jL x : Ω')) ∧ Algebra.adjoin E' (Set.range jL) = ⊤ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j c hφ hc L hL hloc
  classical
  haveI := IsAlgClosure.isAlgebraic (R := E) (K := Ω)
  haveI := IsAlgClosure.isAlgebraic (R := E') (K := Ω')

  obtain ⟨α, rfl⟩ : ∃ α : Ω, E⟮α⟯ = L := by
    obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element E L
    refine ⟨(α₀ : Ω), ?_⟩
    have := congrArg (IntermediateField.map L.val) hα₀
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this
  have hint : IsIntegral E α := Algebra.IsIntegral.isIntegral α
  set α' : Ω' := φ α with hα'
  have hint' : IsIntegral E' α' := Algebra.IsIntegral.isIntegral α'
  set p := minpoly E α with hp
  set m' := minpoly E' α' with hm'
  have hcomp : (algebraMap E' Ω').comp j = (φ : Ω →+* Ω').comp (algebraMap E Ω) := by
    ext x; exact (hφ x).symm
  have key : ∀ β : Ω, φ (aeval β p) = aeval (φ β) (p.map j) := by
    intro β
    rw [aeval_def, aeval_def, eval₂_map, hcomp]
    exact Polynomial.hom_eval₂ p (algebraMap E Ω) (φ : Ω →+* Ω') β
  have hpmon : p.Monic := minpoly.monic hint
  have hqne : p.map j ≠ 0 := (hpmon.map j).ne_zero
  have hdvd : m' ∣ p.map j := minpoly.dvd E' α' (by rw [← key, minpoly.aeval]; simp)
  have hm'root : ∀ σ' : G E' Ω', aeval (σ' α') m' = 0 := by
    intro σ'
    rw [show σ' α' = (σ' : Ω' →ₐ[E'] Ω') α' from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hq : ∀ y : Ω', aeval y m' = 0 → aeval y (p.map j) = 0 := by
    intro y hy
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, hy, zero_mul]

  have horb : ∀ β : Ω, aeval β p = 0 → ∃ τ : Weil h, (τ : G E Ω) α = β := by
    intro β hβ
    have hmin : minpoly E β = minpoly E α :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ hpmon).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 hmin
    obtain ⟨τ, hτ⟩ := hloc σ
    refine ⟨τ, ?_⟩
    have := hτ ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩
    simp only [IntermediateField.algebraMap_apply] at this
    rw [this]; exact hσ

  set L' : IntermediateField E' Ω' := E'⟮α'⟯ with hL'
  have hsub : ∀ x : E⟮α⟯, φ (x : Ω) ∈ L' := by
    let S : IntermediateField E Ω := Subfield.toIntermediateField
      (L'.toSubfield.comap (φ : Ω →+* Ω')) (fun x => by
        show φ (algebraMap E Ω x) ∈ L'
        rw [hφ]; exact L'.algebraMap_mem (j x))
    have hle : E⟮α⟯ ≤ S := IntermediateField.adjoin_simple_le_iff.2
      (show φ α ∈ L' from IntermediateField.mem_adjoin_simple_self E' α')
    intro x
    exact hle x.2
  let jL : E⟮α⟯ →+* L' := RingHom.codRestrict ((φ : Ω →+* Ω').comp (algebraMap E⟮α⟯ Ω)) L' hsub
  refine ⟨L', jL, IntermediateField.adjoin.finiteDimensional hint', ?_, ?_, fun x => rfl, ?_⟩
  ·
    intro σ'
    have h1 : aeval (σ' α') (p.map j) = 0 := hq _ (hm'root σ')
    have h2 : aeval (φ.symm (σ' α')) p = 0 := by
      apply φ.injective; rw [key, φ.apply_symm_apply, h1, map_zero]
    obtain ⟨τ, hτ⟩ := horb _ h2
    refine ⟨c τ, fun x => ?_⟩
    have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
    have hx : (c τ : G E' Ω') α' = σ' α' := by
      rw [← e, hτ, φ.apply_symm_apply]
    have hle : L'.toSubalgebra ≤ AlgHom.equalizer ((c τ : G E' Ω') : Ω' →ₐ[E'] Ω') (σ' : Ω' →ₐ[E'] Ω') := by
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic, Algebra.adjoin_le_iff,
        Set.singleton_subset_iff]
      exact hx
    exact hle x.2
  · rw [IntermediateField.adjoin.finrank hint', IntermediateField.adjoin.finrank hint]
    apply le_antisymm
    · calc m'.natDegree ≤ (p.map j).natDegree := natDegree_le_of_dvd hdvd hqne
        _ = p.natDegree := natDegree_map j
    · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
      haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed E'
      have hsep : p.Separable := (minpoly.irreducible hint).separable
      have hnd : (p.aroots Ω).Nodup := nodup_roots (hsep.map)
      have hm'ne : m' ≠ 0 := minpoly.ne_zero hint'
      have hpne : p ≠ 0 := hpmon.ne_zero
      have himg : (p.aroots Ω).toFinset.image φ ⊆ (m'.aroots Ω').toFinset := by
        intro y hy
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hy
        rw [Multiset.mem_toFinset, mem_aroots] at hβ ⊢
        obtain ⟨τ, rfl⟩ := horb _ hβ.2
        refine ⟨hm'ne, ?_⟩
        have e : φ ((τ : G E Ω) α) = (c τ : G E' Ω') α' := hc τ α
        rw [e]; exact hm'root _
      calc p.natDegree = (p.aroots Ω).card := IsAlgClosed.card_aroots_eq_natDegree.symm
        _ = (p.aroots Ω).toFinset.card := (Multiset.toFinset_card_of_nodup hnd).symm
        _ = ((p.aroots Ω).toFinset.image φ).card := (Finset.card_image_of_injective _ φ.injective).symm
        _ ≤ (m'.aroots Ω').toFinset.card := Finset.card_le_card himg
        _ ≤ (m'.aroots Ω').card := Multiset.toFinset_card_le _
        _ = m'.natDegree := IsAlgClosed.card_aroots_eq_natDegree
  ·
    apply Subalgebra.map_injective (f := L'.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, IntermediateField.range_val]
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (jL x).2
    · have hsg : ({α'} : Set Ω') ⊆ L'.val '' Set.range jL :=
        Set.singleton_subset_iff.2 ⟨jL ⟨α, IntermediateField.mem_adjoin_simple_self E α⟩, ⟨_, rfl⟩, rfl⟩
      refine le_trans ?_ (Algebra.adjoin_mono hsg)
      rw [hL', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint'.isAlgebraic]

end
