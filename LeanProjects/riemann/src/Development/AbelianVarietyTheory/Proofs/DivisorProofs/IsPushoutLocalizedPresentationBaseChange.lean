import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

section LocalizationBaseChange

variable {R R' C' L ν σ : Type} [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R')
  [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C')

theorem localization_baseChange_ext (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (w₁ w₂ : L →+* T)
    (h₁ : ∀ r : R', w₁ (algebraMap C' L (algebraMap R' C' r)) = w₂ (algebraMap C' L (algebraMap R' C' r)))
    (h₂ : ∀ i, w₁ (algebraMap C' L (ξ i)) = w₂ (algebraMap C' L (ξ i))) : w₁ = w₂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.aeval ξ (MvPolynomial.map a h)))
  refine RingHom.ext fun c => ?_
  obtain ⟨P, rfl⟩ := hsurj c
  have e : w₁.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) =
      w₂.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using h₁ r
    · intro i
      simpa using h₂ i
  exact congr($e P)

theorem localization_baseChange_desc (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    (hker : ∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 →
      MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (u : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* T) (v : R' →+* T)
    (huv : ∀ r : R, u (algebraMap R _ r) = v (a r)) :
    ∃ w : L →+* T, (∀ G : MvPolynomial ν R, w (algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G))) =
        u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G))) ∧
      ∀ r : R', w (algebraMap C' L (algebraMap R' C' r)) = v r := by
  let θ : MvPolynomial ν R' →+* T := MvPolynomial.eval₂Hom v (fun i ↦
    u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))))
  have hθ : θ.comp (MvPolynomial.map a) = u.comp ((algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F))
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, θ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← huv]
      rfl
    · intro i
      simp [θ]
  have hθ' : ∀ G, θ (MvPolynomial.map a G) =
      u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) :=
    fun G ↦ congr($hθ G)
  have hunit : IsUnit (θ (MvPolynomial.map a h)) := by
    rw [hθ']
    exact (IsLocalization.Away.algebraMap_isUnit _).map u
  have hspan : Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hθ', (Ideal.Quotient.eq_zero_iff_mem (a := F s) (I := Ideal.span (Set.range F))).2 (Ideal.subset_span ⟨s, rfl⟩),
      map_zero, map_zero]
  have hk : RingHom.ker (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom ≤ RingHom.ker θ := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    have e := RingHom.mem_ker.1 (hspan (hker G hG))
    rw [map_mul] at e
    exact RingHom.mem_ker.2 ((hunit.mul_right_eq_zero).1 e)
  let θ' : C' →+* T := (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨θ, hk⟩
  have hθ'e : ∀ P, θ' (MvPolynomial.aeval ξ P) = θ P := fun P ↦
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hu2 : IsUnit (θ' (MvPolynomial.aeval ξ (MvPolynomial.map a h))) := by
    rw [hθ'e]
    exact hunit
  refine ⟨IsLocalization.Away.lift (MvPolynomial.aeval ξ (MvPolynomial.map a h)) hu2, fun G ↦ ?_, fun r ↦ ?_⟩
  · rw [IsLocalization.Away.lift_eq, hθ'e, hθ']
  · rw [IsLocalization.Away.lift_eq, ← MvPolynomial.aeval_C (R := R') ξ r, hθ'e]
    simp [θ]

end LocalizationBaseChange

theorem isPushout_localization_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  intro R R' C' L ν σ _ _ _ _ a _ _ F h ξ hsurj hF hker hL
  have hI : Ideal.span (Set.range F) ≤
      RingHom.ker ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    exact RingHom.mem_ker.2 (hF s)
  let β := Ideal.Quotient.lift (Ideal.span (Set.range F))
    ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a))
    (fun x hx ↦ RingHom.mem_ker.1 (hI hx))
  have hβ : ∀ G, β (Ideal.Quotient.mk _ G) = MvPolynomial.aeval ξ (MvPolynomial.map a G) := fun G ↦ rfl
  have hu : IsUnit (((algebraMap C' L).comp β) (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
    rw [RingHom.comp_apply, hβ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L :=
    IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) hu
  have hα : ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _
      (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := fun G ↦ by
    simp only [α]
    rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, hβ]
  have hR : ∀ r : R, algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) r =
      algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) :=
    fun r ↦ rfl
  refine ⟨α, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Classical.choose (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r))))) ?_ ?_ ?_), hα⟩
  · ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [hR, hα]
    simp
  · intro s
    obtain ⟨hd1, -⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun G ↦ ?_
    simp only [RingHom.comp_apply]
    rw [hα, hd1]
  · intro s
    obtain ⟨-, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hd2 r
  · intro s m h₁ h₂
    obtain ⟨hd1, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    apply localization_baseChange_ext a h ξ hsurj
    · intro r
      rw [hd2]
      exact congr($h₂ r)
    · intro i
      have e : algebraMap C' L (ξ i) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a (MvPolynomial.X i))) := by
        simp
      rw [e, hd1, ← hα]
      exact congr($h₁ _)

end GlobalTheory.Pinch
