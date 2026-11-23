import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetB

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem valAt'_comp (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  have e : x ⁻¹ᵁ φ ⁻¹ᵁ U = (x ≫ φ) ⁻¹ᵁ U := rfl
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [dif_pos (e ▸ h), dif_pos h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dif_neg (e ▸ h), dif_neg h]

theorem isHolFam_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y') :
    IsHolFam (fun z => e z ≫ φ) := by
  intro U f
  have := hol (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [valAt'_comp] at this
  exact this

set_option backward.isDefEq.respectTransparency false in

theorem jetPt_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y')
    (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y')) (hol' : IsHolFam e') (he : ∀ z, e z ≫ φ = e' z) (m : ℕ) :
    jetPt e hol m ≫ φ = jetPt e' hol' m := by
  have hpt : (jetPt e hol m ≫ φ) (IsLocalRing.closedPoint _) = jetPt e' hol' m (IsLocalRing.closedPoint _) := by
    rw [Scheme.Hom.comp_apply, jetPt_closedPoint, jetPt_closedPoint, ← he 0, Scheme.Hom.comp_apply]
  refine hom_ext_of_local hpt fun U h₁ h₂ => ?_
  have hU : e' 0 cpt ∈ U := by
    have : jetPt e' hol' m (IsLocalRing.closedPoint _) ∈ U :=
      h₂ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [jetPt_closedPoint] at this
  have hU' : φ (e 0 cpt) ∈ U := by
    rw [← Scheme.Hom.comp_apply, he 0]; exact hU
  have k := nbhdPt_comp_appLE (y₀ := e 0 cpt) φ (jetψ e hol m) (jetψ_res e hol m) (jetψ_loc e hol m) U hU' h₁
  refine (k : (jetPt e hol m ≫ φ).appLE U ⊤ h₁ = _).trans ?_
  rw [jetPt_appLE e' hol' m U hU h₂, ← Category.assoc]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  congr 1
  funext z
  rw [valAt'_comp, he z]

set_option backward.isDefEq.respectTransparency false in

theorem jetPt_aug (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ) :
    spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) ≫ jetPt e hol m = e 0 := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) f) →
        e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply, jetψ_apply] at hf
    change IsUnit ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _) at hf
    rw [jetAug_jetOf] at hf
    exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp hf.ne_zero
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hpt := nbhdPt_closedPoint _ hres hloc
  refine hom_ext_of_local (hpt.trans rfl) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  ext f
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, jetψ_apply]
  change (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _ = _
  rw [jetAug_jetOf, valAt'_of _ _ h₂]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
