import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ThickStalkEq

theorem isLocalHom_mk {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (Ideal.Quotient.mk I) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨v, hv⟩ := ha
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : A ⧸ I)
  have h1 : Ideal.Quotient.mk I (a * b - 1) = 0 := by
    rw [map_sub, map_mul, hb, ← hv]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have hm : a * b - 1 ∈ maximalIdeal A := le_maximalIdeal hI h1
  have ha' : a * b ∈ maximalIdeal A := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 hna)
  have h2 : (1 : A) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ ha' hm
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem pow_succ_ne_top (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    maximalIdeal A ^ (e + 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e))

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    Nontrivial (A ⧸ maximalIdeal A ^ (e + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top A e)

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (e + 1)) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

instance (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) :=
  isLocalHom_mk _ (pow_succ_ne_top A e)

theorem eq_of_forall_pow {X : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (u u' : Spec A ⟶ X)
    (h : ∀ e : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u') :
    u = u' := by
  obtain ⟨⟨y, ψ, hψ⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u
  obtain ⟨⟨y', ψ', hψ'⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u'
  have key : ∀ e : ℕ, ∃ h₁ : y = y',
      ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) =
        (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫
          ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) := by
    intro e
    have he := h e
    simp only [SpecToEquivOfLocalRing_symm_apply, ← Spec.map_comp_assoc] at he
    have l1 : IsLocalHom (ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have l2 : IsLocalHom (ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have hinj := (SpecToEquivOfLocalRing X (.of (A ⧸ maximalIdeal A ^ (e + 1)))).symm.injective
      (a₁ := ⟨y, ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l1⟩)
      (a₂ := ⟨y', ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l2⟩)
      (by simpa only [SpecToEquivOfLocalRing_symm_apply] using he)
    obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
    exact ⟨h₁, h₂⟩
  obtain ⟨rfl, -⟩ := key 0
  have hψψ : ψ = ψ' := by
    ext f
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
      Ideal.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ e =>
      obtain ⟨_, h₂⟩ := key e
      simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp] at h₂
      have := congrArg (fun g => g.hom f) h₂
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact Ideal.Quotient.eq.mp this
  subst hψψ
  rfl

end GlobalTheory.ThickStalkEq

namespace GlobalTheory.ThickStalkEq

theorem fromSpecStalk_comp_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G),
    (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b =
      (Over.pullback (thick R (maximalIdeal R) e)).map b') →
    ∀ x : G.left, G.hom x = closedPoint R →
      G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by
  intro R _ _ _ G hG b b' hb x hx
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let A := G.left.presheaf.stalk x
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (G.left.fromSpecStalk x ≫ G.hom)
  have hφ : Spec.map φ = G.left.fromSpecStalk x ≫ G.hom := Spec.map_preimage _
  have h1 : (Spec.map φ) (closedPoint A) = closedPoint R := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg G.hom Scheme.fromSpecStalk_closedPoint).trans hx)
  have hloc : ∀ r ∈ maximalIdeal R, φ.hom r ∈ maximalIdeal A := by
    intro r hr
    have hc : PrimeSpectrum.comap φ.hom (closedPoint A) = closedPoint R := h1
    have : r ∈ (PrimeSpectrum.comap φ.hom (closedPoint A)).asIdeal := by rw [hc]; exact hr
    exact this
  refine eq_of_forall_pow A _ _ (fun e => ?_)
  have hle : maximalIdeal R ^ (e + 1) ≤ (maximalIdeal A ^ (e + 1)).comap φ.hom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hloc) _
  let χ : R ⧸ maximalIdeal R ^ (e + 1) →+* A ⧸ maximalIdeal A ^ (e + 1) :=
    Ideal.quotientMap _ φ.hom hle
  have hw : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫
      G.left.fromSpecStalk x) ≫ G.hom = Spec.map (CommRingCat.ofHom χ) ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, ← hφ, thick, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have := congrArg (fun g => pullback.lift _ _ hw ≫ g.left ≫ pullback.fst _ _) (hb e)
  simp only [Over.pullback_map_left] at this
  rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc] at this
  simpa only [Category.assoc] using this

end GlobalTheory.ThickStalkEq
