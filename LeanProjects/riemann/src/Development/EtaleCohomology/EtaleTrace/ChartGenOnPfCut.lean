import Development.EtaleCohomology.EtaleTrace.GenOutChartPfGen

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def ChartGenMem : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0)

def ChartGenVal : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h ((chartMor i U hx φ).app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

theorem ChartGenOn_of (h1 : ChartGenMem) (h2 : ChartGenVal) : ChartGenOn := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  exact ⟨h1 k p N w i hi U hx φ hφ hη n hn f hf, fun m g hg h => h2 k p N w i hi U hx φ hφ hη n hn f hf m g hg h⟩

theorem ChartGenMem_pf : ChartGenMem := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  have e1 : chartMor i U hx φ = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one := by
    rw [chartMor, Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp_assoc]; rfl
  have e2 : chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f =
      U.ι ⁻¹ᵁ X.basicOpen (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf)) := by
    rw [e1, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen _ hx zero_lt_one hf hn, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  rw [e2]
  change genericPoint X ∈ X.basicOpen _ ↔ _
  rw [Scheme.mem_basicOpen _ _ _ hη]
  have h' : (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X)))
      (X.presheaf.germ U _ hη (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf))) =
        eval₂ (kHom p) w f / w i ^ n := by
    have h := hφ (genericPoint X) hη n (f ^ 1) (by simpa using hf)
    exact h.trans (by rw [pow_one])
  rw [isUnit_iff_ne_zero, ← (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X))).injective.ne_iff,
    map_zero, h']
  simp [hi]

end LateralTheory.EtaleTrace.Cov
