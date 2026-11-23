import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.PairDich

theorem isUnit_ι_appTop {T : Scheme.{0}} (W : T.Opens) (E : Γ(T, ⊤)) (h : W ≤ T.basicOpen E) :
    IsUnit (W.ι.appTop E) := by
  refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun w _ => ?_
  have hw : w ∈ W.ι ⁻¹ᵁ T.basicOpen E := h w.2
  rw [Scheme.preimage_basicOpen_top] at hw
  exact (Scheme.mem_basicOpen_top _ _ _).1 hw

theorem mem_basicOpen_or {T : Scheme.{0}} (E : Γ(T, ⊤)) (t : T) :
    t ∈ T.basicOpen E ∨ t ∈ T.basicOpen (1 - E) := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem comp_rule {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {T : Scheme.{0}}
    (y : T ⟶ Spec (CommRingCat.of B)) (a : A) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (y ≫ Spec.map (CommRingCat.ofHom g)).appTop).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom (g a) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.EtC.PairDich

namespace GlobalTheory.EtC.PairDich

theorem pair_dich : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  intro A A' _ _ _ f e u he hu T y y' hyy
  let φ : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y.appTop).hom
  let φ' : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y'.appTop).hom
  have hA : ∀ r : A, φ (algebraMap A A' r) = φ' (algebraMap A A' r) := by
    intro r
    have := congrArg (fun m : T ⟶ Spec (CommRingCat.of A) =>
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ m.appTop).hom r) hyy
    simp only at this
    rw [comp_rule, comp_rule] at this
    exact this
  letI : Algebra A Γ(T, ⊤) := (φ.comp (algebraMap A A')).toAlgebra
  let φa : A' →ₐ[A] Γ(T, ⊤) := ⟨φ, fun _ => rfl⟩
  let φa' : A' →ₐ[A] Γ(T, ⊤) := ⟨φ', fun r => (hA r).symm⟩
  let ψ := Algebra.TensorProduct.productMap φa φa'
  have hE : ∀ a : A', (φ a - φ' a) * ψ e = 0 := by
    intro a
    have := congrArg ψ (he a)
    rw [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, mul_one, one_mul, map_zero] at this
    exact this
  have hF : ψ (algebraMap A _ f) * ψ u = 1 - ψ e := by rw [← map_mul, hu, map_sub, map_one]
  have hψf : ψ (algebraMap A _ f) = φ (algebraMap A A' f) := by rw [AlgHom.commutes]; rfl
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    have key : ∀ G : Γ(T, ⊤), t ∈ T.basicOpen G → ∃ W : T.Opens, IsAffine W ∧ t ∈ W ∧ IsUnit (W.ι.appTop G) := by
      intro G hG
      obtain ⟨W0, hW, htW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hG
      exact ⟨W0, hW, htW, isUnit_ι_appTop W0 G hWle⟩
    rcases mem_basicOpen_or (ψ e) t with h1 | h2
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h1
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inl ?_⟩
      apply ext_to_Spec
      simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
      ext a
      have h0 := congrArg W.ι.appTop.hom (hE a)
      rw [map_mul, map_sub, map_zero, hunit.mul_left_eq_zero, sub_eq_zero] at h0
      exact h0
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h2
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inr ?_⟩
      rw [← Category.assoc, comp_rule, Scheme.Hom.comp_appTop]
      have h0 := congrArg W.ι.appTop.hom hF
      rw [map_mul, hψf] at h0
      rw [← h0] at hunit
      exact isUnit_of_mul_isUnit_left hunit
  · rintro V W g k (h | h)
    · exact Or.inl (by rw [Category.assoc, h, Category.assoc])
    · right
      have hc : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((k ≫ g) ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop
          = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (g ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop) ≫ k.appTop := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [hc, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h.map _

end GlobalTheory.EtC.PairDich
