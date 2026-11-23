import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportB
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecArtin
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime]
  (m : Model K p)

theorem toAb_surjective' (F : Type) [Field F] (a : Field.absoluteGaloisGroupAbelianization F) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, toAb F g = a := QuotientGroup.mk'_surjective _ a

theorem toAb_inv_mul (F : Type) [Field F] (g h : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    toAb F (g⁻¹ * h) = (toAb F g)⁻¹ * toAb F h := by
  exact (map_mul (toAb F) g⁻¹ h).trans (congrArg (· * toAb F h) (map_inv (toAb F) g))

theorem continuous_symm_of_isHomeomorph {G H : Type*} [Mul G] [Mul H] [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃* H) (he : IsHomeomorph e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  have : e.symm ⁻¹' s = e '' s :=
    (Set.image_eq_preimage_of_inverse e.left_inv e.right_inv).symm ▸ rfl
  rw [this]
  exact he.isOpenMap s hs

theorem Model.isArtinK_of_isLocalArtinMap {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K) (h : IsLocalArtinMap K Art) :
    IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hsymm : Continuous m.eU.symm := continuous_symm_of_isHomeomorph _ m.isHomeomorph_eU

  have key : ∀ (x' : (m.K')ˣ) (g' : GK p m.K'),
      toAbK p m.K' g' = ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) x' →
      toAb K (φ.symm g') = Art (m.eU.symm x') := by
    intro x' g' hg
    apply ψ.injective
    rw [hψφ, MulEquiv.apply_symm_apply, hg]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hψ.continuous.comp (h1.comp hsymm)
  · exact ψ.injective.comp (h2.comp m.eU.symm.injective)
  · exact (hψ.surjective.denseRange.comp h3 hψ.continuous).comp m.eU.symm.surjective.denseRange
      (hψ.continuous.comp h1)
  · intro π' hπ' g' hg'
    have := h4 (m.eU.symm π') ((m.isUniformiser_iff _).2 (by rwa [MulEquiv.apply_symm_apply]))
      (φ.symm g') (key _ _ hg')
    rw [m.isFrobeniusLift_iff hφ, MulEquiv.apply_symm_apply] at this
    exact this
  · intro L' hL'
    obtain ⟨L, hL⟩ := m.exists_corr' L' hL'.le
    have hab : IsFiniteAbelian K L := (m.isFiniteAbelian_iff hL).2 hL'
    obtain ⟨h6, h7⟩ := h5 L hab
    refine ⟨?_, ?_⟩
    · intro g'
      obtain ⟨x, hx⟩ := h6 (abRestrict K L hab (toAb K (φ.symm g')))
      obtain ⟨g2, hg2⟩ := toAb_surjective' K (Art x)
      refine ⟨m.eU x, φ g2, ?_, ?_⟩
      · rw [← hψφ, hg2]
        show _ = ψ (Art (m.eU.symm (m.eU x)))
        rw [MulEquiv.symm_apply_apply]
      · have : abRestrict K L hab (toAb K (g2⁻¹ * φ.symm g')) = 1 := by
          rw [toAb_inv_mul, map_mul, map_inv, hg2, ← hx]
          exact inv_mul_cancel _
        rw [m.abRestrict_eq_one_iff hφ hL hab] at this
        simpa using this
    · intro x' g' hg'
      have hk := key _ _ hg'
      have e1 : m.eU.symm x' ∈ ((abRestrict K L hab).comp Art).ker ↔ m.eU.symm x' ∈ normGroup K L := by
        rw [h7]
      rw [m.mem_normGroup_iff hL hab.finiteDimensional, MulEquiv.apply_symm_apply, MonoidHom.mem_ker,
        MonoidHom.comp_apply, ← hk, m.abRestrict_eq_one_iff hφ hL hab, MulEquiv.apply_symm_apply] at e1
      exact e1

theorem Model.isLocalArtinMap_of_isArtinK {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K)
    (h : IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom)) :
    IsLocalArtinMap K Art := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hψs : Continuous ψ.symm := continuous_symm_of_isHomeomorph _ hψ
  have hArt : ∀ x, ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x) = ψ (Art x) := by
    intro x
    show ψ (Art (m.eU.symm (m.eU x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hfun : (Art : Kˣ → _) =
      ψ.symm ∘ ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) ∘ m.eU := by
    funext x
    show _ = ψ.symm (((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x))
    rw [hArt, MulEquiv.symm_apply_apply]
  have key : ∀ (x : Kˣ) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), toAb K g = Art x →
      toAbK p m.K' (φ g) = ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) (m.eU x) := by
    intro x g hg
    rw [hArt, ← hψφ, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hψs.comp (h1.comp m.isHomeomorph_eU.continuous)
  · rw [hfun]
    exact ψ.symm.injective.comp (h2.comp m.eU.injective)
  · rw [hfun]
    exact (ψ.symm.surjective.denseRange.comp h3 hψs).comp m.eU.surjective.denseRange
      (hψs.comp h1)
  · intro π hπ g hg
    rw [m.isFrobeniusLift_iff hφ]
    exact h4 (m.eU π) ((m.isUniformiser_iff _).1 hπ) (φ g) (key _ _ hg)
  · intro L hab
    obtain ⟨L', -, hL⟩ := m.exists_corr L
    have hL' : IsAbLK p m.K' L' := (m.isFiniteAbelian_iff hL).1 hab
    obtain ⟨h6, h7⟩ := h5 L' hL'
    refine ⟨?_, ?_⟩
    · intro τ
      have := hab.isGalois
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (AlgebraicClosure K) τ
      obtain ⟨x', g', hg', hmem⟩ := h6 (φ g)
      refine ⟨m.eU.symm x', ?_⟩
      have e1 : toAb K (φ.symm g') = Art (m.eU.symm x') := by
        apply ψ.injective
        rw [hψφ, MulEquiv.apply_symm_apply, hg']
        rfl
      have e2 : abRestrict K L hab (toAb K ((φ.symm g')⁻¹ * g)) = 1 := by
        rw [m.abRestrict_eq_one_iff hφ hL hab]
        simpa using hmem
      rw [toAb_inv_mul, map_mul, map_inv, inv_mul_eq_one] at e2
      rw [MonoidHom.comp_apply, ← e1, e2, abRestrict_mk, hg]
    · ext x
      obtain ⟨g, hg⟩ := toAb_surjective' K (Art x)
      rw [m.mem_normGroup_iff hL hab.finiteDimensional, ← h7 (m.eU x) (φ g) (key _ _ hg), MonoidHom.mem_ker,
        MonoidHom.comp_apply, ← hg, m.abRestrict_eq_one_iff hφ hL hab]

theorem Model.isLocalArtinMap_iff {φ} (hφ : m.IsGalIso φ)
    (ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K') (hψ : IsHomeomorph ψ)
    (hψφ : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g))
    (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K) :
    IsLocalArtinMap K Art ↔
      IsArtinK p m.K' ((ψ.toMonoidHom.comp Art).comp m.eU.symm.toMonoidHom) :=
  ⟨m.isArtinK_of_isLocalArtinMap hφ ψ hψ hψφ Art, m.isLocalArtinMap_of_isArtinK hφ ψ hψ hψφ Art⟩

theorem Model.artin_reciprocity_of_model (h : ∃ Art, IsArtinK p m.K' Art) : LocalReciprocity K := by
  obtain ⟨Art', hA⟩ := h
  obtain ⟨φ, hφ⟩ := m.exists_isGalIso
  obtain ⟨ψ, hψ, hψφ⟩ := m.exists_abIso hφ
  refine ⟨(ψ.symm.toMonoidHom.comp Art').comp m.eU.toMonoidHom, ?_⟩
  rw [m.isLocalArtinMap_iff hφ ψ hψ hψφ]
  convert hA using 1
  ext x
  simp

theorem artin_reciprocity_char_zero (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] : LocalReciprocity K := by
  obtain ⟨p, hp, ⟨m⟩⟩ := exists_model K
  exact m.artin_reciprocity_of_model (exists_isArtinK m.fin)

end ReciprocityTheory.DiscreteGroups.LocalClassField
