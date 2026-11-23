import Mathlib
import Development.EtaleCohomology.EtaleTrace.ChartGenOnPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeAppLEComposition.Cb

private lemma proj_germ_id {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {x f g : A} {n m : ℕ} (hx : x ∈ 𝒜 1) (hf : f ∈ 𝒜 n) (hf' : f ∈ 𝒜 (n • 1)) (hg : g ∈ 𝒜 (m • n))
    (hg' : g ∈ 𝒜 ((m * n) • 1))
    (y : Proj 𝒜) (hyf : y ∈ Proj.basicOpen 𝒜 f) (hyx : y ∈ Proj.basicOpen 𝒜 x) :
    (Proj 𝒜).presheaf.germ _ y hyf (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf m g hg)) *
      ((Proj 𝒜).presheaf.germ _ y hyx (Proj.awayToSection 𝒜 x (Away.mk 𝒜 hx n f hf'))) ^ m =
    (Proj 𝒜).presheaf.germ _ y hyx (Proj.awayToSection 𝒜 x (Away.mk 𝒜 hx (m * n) g hg')) := by
  apply (Proj.stalkIso' 𝒜 y).injective
  refine (map_mul (Proj.stalkIso' 𝒜 y) _ _).trans ?_
  refine (congrArg (Proj.stalkIso' 𝒜 y _ * ·) (map_pow (Proj.stalkIso' 𝒜 y) _ _)).trans ?_
  erw [Proj.stalkIso'_germ, Proj.stalkIso'_germ, Proj.stalkIso'_germ]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply, ProjectiveSpectrum.Proj.awayToSection_apply,
    ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  rw [← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul]
  apply IsLocalization.mk'_eq_of_eq
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
  ring

private lemma ι_appLE {X : Scheme.{0}} (U : X.Opens) (h : ⊤ ≤ U.ι ⁻¹ᵁ U) : U.ι.appLE U ⊤ h = U.topIso.inv := by
  rw [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
  erw [← Functor.map_comp]
  rfl

private lemma appLE_eq_comp_appTop {X Y Z : Scheme.{0}} (T : X ⟶ Y) (a : Y ⟶ Z) (C : X ⟶ Z) (hC : T ≫ a = C) (W : Z.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ W) (h : ⊤ ≤ C ⁻¹ᵁ W) : C.appLE W ⊤ h = a.appLE W ⊤ ha ≫ T.appTop := by
  subst hC
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_comp_appLE T a W ⊤ ⊤ ha (fun _ _ => trivial)).symm

private lemma away_appLE {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {x : A} {d : ℕ} (hx : x ∈ 𝒜 d) (hd : 0 < d) (c : Away 𝒜 x)
    (h : ⊤ ≤ Proj.awayι 𝒜 x hx hd ⁻¹ᵁ Proj.basicOpen 𝒜 x) :
    (Proj.awayι 𝒜 x hx hd).appLE _ ⊤ h (Proj.awayToSection 𝒜 x c) =
      (Scheme.ΓSpecIso (.of (Away 𝒜 x))).inv c := by
  have h1 := congr($(Proj.basicOpenToSpec_app_top 𝒜 x) ((Scheme.ΓSpecIso _).inv c))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h1
  have h2 : (Proj.awayι 𝒜 x hx hd).appLE _ ⊤ h =
      (Proj.basicOpen 𝒜 x).topIso.inv ≫ (Proj.basicOpenIsoSpec 𝒜 x hx hd).inv.appTop := by
    rw [← ι_appLE (Proj.basicOpen 𝒜 x) (fun _ _ => by simp)]
    exact appLE_eq_comp_appTop _ _ _ rfl _ _ h
  have h3 : (Proj.basicOpenIsoSpec 𝒜 x hx hd).hom.appTop ≫ (Proj.basicOpenIsoSpec 𝒜 x hx hd).inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have h1' : (Proj.basicOpenIsoSpec 𝒜 x hx hd).hom.appTop ((Scheme.ΓSpecIso (.of (Away 𝒜 x))).inv c) =
      (Proj.basicOpen 𝒜 x).topIso.inv (Proj.awayToSection 𝒜 x c) := h1
  rw [h2, ConcreteCategory.comp_apply, ← h1', ← ConcreteCategory.comp_apply, h3]
  rfl

private lemma chart_germ {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {V : Scheme.{0}} {x : A} {d : ℕ} (hx : x ∈ 𝒜 d) (hd : 0 < d) (ψ : Away 𝒜 x →+* Γ(V, ⊤)) (c : Away 𝒜 x)
    (y : V) (hy : y ∈ (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 x hx hd) ⁻¹ᵁ Proj.basicOpen 𝒜 x) :
    V.presheaf.germ _ y hy ((V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 x hx hd).app _
      (Proj.awayToSection 𝒜 x c)) = V.presheaf.germ ⊤ y trivial (ψ c) := by
  have ha : ⊤ ≤ Proj.awayι 𝒜 x hx hd ⁻¹ᵁ Proj.basicOpen 𝒜 x := by
    intro z _
    change Proj.awayι 𝒜 x hx hd z ∈ Proj.basicOpen 𝒜 x
    rw [← Proj.opensRange_awayι 𝒜 x hx hd]
    exact ⟨z, rfl⟩
  have hC : ⊤ ≤ (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 x hx hd) ⁻¹ᵁ Proj.basicOpen 𝒜 x := by
    intro z _
    exact ha (show _ ∈ (⊤ : (Spec (CommRingCat.of (Away 𝒜 x))).Opens) from trivial)
  have h5 : (Scheme.ΓSpecIso (.of (Away 𝒜 x))).inv ≫ (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have h6 := appLE_eq_comp_appTop (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)) (Proj.awayι 𝒜 x hx hd) _
    (Category.assoc _ _ _) _ ha hC
  have h7 : (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 x hx hd).appLE _ ⊤ hC
      (Proj.awayToSection 𝒜 x c) = ψ c := by
    rw [h6, ConcreteCategory.comp_apply, away_appLE, ← ConcreteCategory.comp_apply, h5]
    rfl
  rw [← h7, Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE hC) y trivial _).symm

private lemma top_germ {X : Scheme.{0}} (U : X.Opens) (y : U) (s : Γ(X, U)) :
    U.toScheme.presheaf.germ ⊤ y trivial (U.topIso.inv s) =
      (U.ι.stalkMap y).hom (X.presheaf.germ U (U.ι y) y.2 s) := by
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [← ι_appLE U (fun _ _ => by simp), Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  exact TopCat.Presheaf.germ_res_apply U.toScheme.presheaf
    (homOfLE (fun _ _ => by simp) : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ U) y trivial _

private lemma alg_generic (X : Scheme.{0}) [IsIntegral X] (a : X.presheaf.stalk (genericPoint X)) :
    (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _
      (stalkFunctionFieldAlgebra X (genericPoint X))) a = a :=
  congr($(X.presheaf.stalkSpecializes_refl (genericPoint X)) a)

private lemma alg_id {K R : Type*} [Field K] [CommRing R] (J : K →+* R) {W F G : K} (hW : W ≠ 0) {S : R} {n m : ℕ}
    (h : S * J (F / W ^ n) ^ m = J (G / W ^ (m * n))) : S * J F ^ m = J G := by
  obtain ⟨a, rfl⟩ : ∃ a, F = a * W ^ n := ⟨F / W ^ n, by field_simp⟩
  obtain ⟨b, rfl⟩ : ∃ b, G = b * W ^ (m * n) := ⟨G / W ^ (m * n), by field_simp⟩
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hW), mul_div_cancel_right₀ _ (pow_ne_zero _ hW)] at h
  rw [map_mul, map_mul, mul_pow, ← mul_assoc, h, map_pow, map_pow, ← pow_mul, mul_comm n m]

private lemma units_mul_relation_rearrange_commRing {R R' : Type*} [CommRing R] [CommRing R'] (J : R →+* R') {P Q T : R} {m : ℕ}
    (h : P * Q ^ m = T) {S q t : R'} (h1 : J P = S) (h2 : J Q = q) (h3 : J T = t) : S * q ^ m = t := by
  subst h1 h2 h3
  rw [← map_pow, ← map_mul, h]

theorem _root_.SchemeAppLEComposition.Cb.etale_projective_chart_generic_valuation_identity :
    LateralTheory.EtaleTrace.Cov.ChartGenVal := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf m g hg h
  have hf' : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • 1) := by simpa using hf
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k ((m * n) • 1) := by simpa using hg
  have hall : ∀ z : U.toScheme, z ∈ LateralTheory.EtaleTrace.Cov.chartMor i U hx φ ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
    intro z
    change Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one _ ∈
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
    rw [← Proj.opensRange_awayι _ _ hx zero_lt_one]
    exact ⟨_, rfl⟩
  have hc : ∀ c, U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ (hall _)
      ((LateralTheory.EtaleTrace.Cov.chartMor i U hx φ).app _ (Proj.awayToSection _ (MvPolynomial.X i) c)) =
      (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (X.presheaf.germ U (U.ι ⟨genericPoint X, hη⟩) hη (φ c)) :=
    fun c => (chart_germ _ hx zero_lt_one (U.topIso.inv.hom.comp φ) c _ (hall _)).trans (top_germ U _ _)
  have hs : ∀ (W : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).Opens) (hW : LateralTheory.EtaleTrace.Cov.chartMor i U hx φ ⟨genericPoint X, hη⟩ ∈ W) (s : Γ(Proj (homogeneousSubmodule (Fin (N + 1)) k), W)),
      (LateralTheory.EtaleTrace.Cov.chartMor i U hx φ |>.stalkMap ⟨genericPoint X, hη⟩).hom ((Proj (homogeneousSubmodule (Fin (N + 1)) k)).presheaf.germ W _ hW s) =
        U.toScheme.presheaf.germ (LateralTheory.EtaleTrace.Cov.chartMor i U hx φ ⁻¹ᵁ W) ⟨genericPoint X, hη⟩ hW
          ((LateralTheory.EtaleTrace.Cov.chartMor i U hx φ).app W s) :=
    fun W hW s => Scheme.Hom.germ_stalkMap_apply _ W _ hW s
  have hE := (alg_generic X _).symm.trans (hφ (genericPoint X) hη n f hf')
  have hB := (alg_generic X _).symm.trans (hφ (genericPoint X) hη (m * n) g hg')
  let J : X.functionField →+* U.toScheme.presheaf.stalk ⟨genericPoint X, hη⟩ :=
    (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom
  refine alg_id J hi (n := n) (m := m) ?_
  exact units_mul_relation_rearrange_commRing (LateralTheory.EtaleTrace.Cov.chartMor i U hx φ |>.stalkMap ⟨genericPoint X, hη⟩).hom
    (proj_germ_id _ hx hf hf' hg hg' _ h (hall ⟨genericPoint X, hη⟩))
    (hs _ h _) ((hs _ _ _).trans ((hc _).trans (congrArg J hE))) ((hs _ _ _).trans ((hc _).trans (congrArg J hB)))

end SchemeAppLEComposition.Cb
end
end
