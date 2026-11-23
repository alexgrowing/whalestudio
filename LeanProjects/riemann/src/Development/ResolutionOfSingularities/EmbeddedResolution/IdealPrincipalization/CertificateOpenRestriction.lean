import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

noncomputable def comapSubscheme {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    (D.comap f).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.comap f) D f (D.le_map_comap f)

theorem comapSubscheme_comp {V W : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData) :
    comapSubscheme f D ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  simp [comapSubscheme]

theorem comapSubscheme_comp_assoc {V W T : Scheme.{u}} (f : V ⟶ W) (D : W.IdealSheafData)
    (g : W ⟶ T) :
    comapSubscheme f D ≫ D.subschemeι ≫ g = (D.comap f).subschemeι ≫ f ≫ g := by
  rw [← Category.assoc, comapSubscheme_comp, Category.assoc]

structure OpenImmersionStability (k : Type u) [Field k] : Prop where
  comap_nonzeroOnComponents :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (J : W.IdealSheafData),
      NonzeroOnComponents J → NonzeroOnComponents (J.comap f)
  isOpenImmersion_comapSubscheme :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (D : W.IdealSheafData),
      IsOpenImmersion (comapSubscheme f D)
  comap_isSmoothDivisor :
    ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
      (p : W ⟶ Spec (CommRingCat.of k)) (D : W.IdealSheafData),
      IsSmoothDivisor p D → IsSmoothDivisor (f ≫ p) (D.comap f)

private theorem coe_support_comap {V W : Scheme.{u}} (f : V ⟶ W) (Z : W.IdealSheafData) :
    ((Z.comap f).support : Set ↥V) = ⇑f.base ⁻¹' ((Z.support : Set ↥W)) := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

private theorem preimage_base_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (S : Set ↥C) :
    ⇑(a ≫ b).base ⁻¹' S = ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) := by
  ext w
  exact Iff.rfl

private theorem preimage_base_preimage_base_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (e : a ≫ b = c ≫ d) (S : Set ↥D) :
    ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) = ⇑c.base ⁻¹' (⇑d.base ⁻¹' S) := by
  rw [← preimage_base_comp, ← preimage_base_comp, e]

private theorem principalizationCertificate_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p₁ p₂ : A ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : A.IdealSheafData} {m : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : PrincipalizationCertificate A p₁ I₁ m Mem₁ Z₁) (hp : p₁ = p₂) (hI : I₁ = I₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : PrincipalizationCertificate A p₂ I₂ m Mem₂ Z₂ := by
  subst hp; subst hI; subst hM; subst hZ; exact h

private theorem orderCertificate_congr {k : Type u} [Field k] {A : Scheme.{u}}
    {p₁ p₂ : A ⟶ Spec (CommRingCat.of k)} {N₁ N₂ : A.IdealSheafData} {μ : ℕ}
    {Mem₁ Mem₂ : Set ↥A} {Z₁ Z₂ : A.IdealSheafData}
    (h : OrderCertificate A p₁ N₁ μ Mem₁ Z₁) (hp : p₁ = p₂) (hN : N₁ = N₂) (hM : Mem₁ = Mem₂)
    (hZ : Z₁ = Z₂) : OrderCertificate A p₂ N₂ μ Mem₂ Z₂ := by
  subst hp; subst hN; subst hM; subst hZ; exact h

private def IsPrincipalizationCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (I : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (⇑f.base ⁻¹' Mem) (Z.comap f)

private def IsOrderCertificateOnOpens {k : Type u} [Field k] (W : Scheme.{u})
    (p : W ⟶ Spec (CommRingCat.of k)) (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W)
    (Z : W.IdealSheafData) : Prop :=
  ∀ (V : Scheme.{u}) (f : V ⟶ W), IsOpenImmersion f →
    OrderCertificate V (f ≫ p) (N.comap f) μ (⇑f.base ⁻¹' Mem) (Z.comap f)

private theorem comapPrincipalizationCertificate_of_support_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap]
  exact Set.preimage_mono h

private theorem comapOrderCertificate_of_support_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : ((Z.support : Set ↥W)) ⊆ Mem) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f _hf
  refine OrderCertificate.memory ?_
  rw [coe_support_comap]
  exact Set.preimage_mono h

private theorem comapPrincipalizationCertificate_of_two_le {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hm : 2 ≤ m) : IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  exact PrincipalizationCertificate.large hm

private theorem comapOrderCertificate_of_two_le {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (hmu : 2 ≤ μ) : IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f _hf
  exact OrderCertificate.large hmu

private theorem comapPrincipalizationCertificate_of_mul_of_order {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (M N : W.IdealSheafData) (μ : ℕ) (hI : I = M * N)
    (hM : ((M.support : Set ↥W)) ⊆ Mem) (hmu : m ≤ μ)
    (hZ : ((Z.support : Set ↥W)) ⊆ orderAtLeastLocus N μ) (ih : IsOrderCertificateOnOpens W p N μ Mem Z) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  refine PrincipalizationCertificate.toOrder (M.comap f) (N.comap f) μ ?_ ?_ hmu ?_ (ih V f hf)
  · rw [hI, Scheme.IdealSheafData.comap_mul]
  · rw [coe_support_comap]
    exact Set.preimage_mono hM
  · rw [coe_support_comap]
    intro y hy
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff N μ (f.base y)).mp (hZ hy))
      (orderAt_le_orderAt_comap f N y)

private theorem comapPrincipalizationCertificate_of_open_cover {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsPrincipalizationCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine PrincipalizationCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine principalizationCertificate_congr (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]

private theorem comapOrderCertificate_of_open_cover {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support),
      IsOrderCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) μ
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine OrderCertificate.localize (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (f.base y) (hsup y hy)) ≫ (U (f.base y) (hsup y hy)).ι
      = (f ⁻¹ᵁ U (f.base y) (hsup y hy)).ι ≫ f := morphismRestrict_ι ..
  refine orderCertificate_congr (ih (f.base y) (hsup y hy) _ (f ∣_ U (f.base y) (hsup y hy))
    inferInstance) ?_ ?_ ?_ ?_
  · rw [← Category.assoc, e1, Category.assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  · exact preimage_base_preimage_base_of_comp_eq e1 Mem
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]

private theorem isSmoothDivisor_comap_morphismRestrict {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData)
    (h : IsSmoothDivisor (U'.ι ≫ p) Hd) :
    IsSmoothDivisor ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)) (Hd.comap (f ∣_ U')) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have h2 := hin.comap_isSmoothDivisor (f ∣_ U') (U'.ι ≫ p) Hd h
  have e4 : (f ∣_ U') ≫ (U'.ι ≫ p) = (f ⁻¹ᵁ U').ι ≫ (f ≫ p) := by
    rw [← Category.assoc, e1, Category.assoc]
  rwa [e4] at h2

private theorem support_comap_morphismRestrict_subset {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (K : W.IdealSheafData)
    (h : ((K.comap U'.ι).support : Set ↥U'.toScheme) ⊆ ((Hd.support : Set ↥U'.toScheme))) :
    ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme)) ⊆
      (((Hd.comap (f ∣_ U')).support : Set ↥(f ⁻¹ᵁ U').toScheme)) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap (f ∣_ U') (K.comap U'.ι), coe_support_comap (f ∣_ U') Hd]
  exact Set.preimage_mono h

private theorem isOpen_preimage_support_comap_morphismRestrict {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (K : W.IdealSheafData)
    (h : IsOpen (⇑Hd.subschemeι.base ⁻¹'
      (((K.comap U'.ι).support : Set ↥U'.toScheme)))) :
    IsOpen (⇑(Hd.comap (f ∣_ U')).subschemeι.base ⁻¹'
      ((((K.comap f).comap (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme))) := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (f ⁻¹ᵁ U').ι = (K.comap U'.ι).comap (f ∣_ U') := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, e1]
  rw [e5, coe_support_comap (f ∣_ U') (K.comap U'.ι),
    preimage_base_preimage_base_of_comp_eq (comapSubscheme_comp (f ∣_ U') Hd).symm
      (((K.comap U'.ι).support : Set ↥U'.toScheme))]
  exact h.preimage (comapSubscheme (f ∣_ U') Hd).base.hom.continuous

private theorem nonzeroOnComponents_comap_comapSubscheme {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (Jz : Hd.subscheme.IdealSheafData)
    (h : NonzeroOnComponents Jz) :
    NonzeroOnComponents (Jz.comap (comapSubscheme (f ∣_ U') Hd)) := by
  have : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  exact hin.comap_nonzeroOnComponents (comapSubscheme (f ∣_ U') Hd) Jz h

private theorem exists_isOpen_comap_eq_comap_morphismRestrict {V W : Scheme.{u}} (f : V ⟶ W) (U' : W.Opens)
    (Hd : U'.toScheme.IdealSheafData) (N : W.IdealSheafData) (Mem : Set ↥W)
    (Jz : Hd.subscheme.IdealSheafData)
    (h : ∀ x : ↥Hd.subscheme, (Hd.subschemeι ≫ U'.ι).base x ∉ Mem →
      ∃ V₀ : Hd.subscheme.Opens, x ∈ V₀ ∧
        Jz.comap V₀.ι = ((N.comap U'.ι).comap Hd.subschemeι).comap V₀.ι)
    (x : ↥(Hd.comap (f ∣_ U')).subscheme)
    (hx : ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x ∉ ⇑f.base ⁻¹' Mem) :
    ∃ V₁ : (Hd.comap (f ∣_ U')).subscheme.Opens, x ∈ V₁ ∧
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)).comap V₁.ι =
        (((N.comap f).comap (f ⁻¹ᵁ U').ι).comap
          (Hd.comap (f ∣_ U')).subschemeι).comap V₁.ι := by
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have h9 : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x)
      = f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) :=
    congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t.base x) e3
  have hx' : (Hd.subschemeι ≫ U'.ι).base ((comapSubscheme (f ∣_ U') Hd).base x) ∉ Mem := by
    intro hmem
    apply hx
    show f.base (((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base x) ∈ Mem
    rw [← h9]
    exact hmem
  obtain ⟨V₀, hxV₀, hV₀⟩ := h _ hx'
  refine ⟨(comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀, hxV₀, ?_⟩
  have hc := congrArg (fun K => Scheme.IdealSheafData.comap K
      ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀)) hV₀
  have e7 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ comapSubscheme (f ∣_ U') Hd
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι := (morphismRestrict_ι ..).symm
  have e8 : ((comapSubscheme (f ∣_ U') Hd) ⁻¹ᵁ V₀).ι ≫ (Hd.comap (f ∣_ U')).subschemeι ≫
        (f ⁻¹ᵁ U').ι ≫ f
      = ((comapSubscheme (f ∣_ U') Hd) ∣_ V₀) ≫ V₀.ι ≫ Hd.subschemeι ≫ U'.ι := by
    rw [← e3, ← Category.assoc, e7, Category.assoc]
  simp only [← Scheme.IdealSheafData.comap_comp] at hc ⊢
  rw [e7, e8]
  exact hc

private theorem principalizationCertificate_comapSubscheme_of_isOpenImmersion {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {V W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : W.Opens) (Hd : U'.toScheme.IdealSheafData) (Z : W.IdealSheafData) (μ : ℕ)
    (Mem : Set ↥W) (Jz : Hd.subscheme.IdealSheafData)
    (h : IsPrincipalizationCertificateOnOpens Hd.subscheme (Hd.subschemeι ≫ (U'.ι ≫ p)) Jz μ
      (⇑(Hd.subschemeι ≫ U'.ι).base ⁻¹' Mem) ((Z.comap U'.ι).comap Hd.subschemeι)) :
    PrincipalizationCertificate (Hd.comap (f ∣_ U')).subscheme
      ((Hd.comap (f ∣_ U')).subschemeι ≫ ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)))
      (Jz.comap (comapSubscheme (f ∣_ U') Hd)) μ
      (⇑((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι).base ⁻¹' (⇑f.base ⁻¹' Mem))
      (((Z.comap f).comap (f ⁻¹ᵁ U').ι).comap (Hd.comap (f ∣_ U')).subschemeι) := by
  have hq : IsOpenImmersion (comapSubscheme (f ∣_ U') Hd) :=
    hin.isOpenImmersion_comapSubscheme (f ∣_ U') Hd
  have e1 : (f ∣_ U') ≫ U'.ι = (f ⁻¹ᵁ U').ι ≫ f := morphismRestrict_ι ..
  have e2 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ∣_ U') := comapSubscheme_comp ..
  have e3 : comapSubscheme (f ∣_ U') Hd ≫ Hd.subschemeι ≫ U'.ι
      = (Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι ≫ f := by
    rw [← Category.assoc, e2, Category.assoc, e1]
  have e3' : comapSubscheme (f ∣_ U') Hd ≫ (Hd.subschemeι ≫ U'.ι)
      = ((Hd.comap (f ∣_ U')).subschemeι ≫ (f ⁻¹ᵁ U').ι) ≫ f := by
    rw [Category.assoc]; exact e3
  refine principalizationCertificate_congr (h _ (comapSubscheme (f ∣_ U') Hd) hq) ?_ rfl ?_ ?_
  · have h5 := congrArg (fun t : (Hd.comap (f ∣_ U')).subscheme ⟶ W => t ≫ p) e3
    simpa only [Category.assoc] using h5
  · exact preimage_base_preimage_base_of_comp_eq e3' Mem
  · simp only [← Scheme.IdealSheafData.comap_comp]
    rw [e3]

private theorem comapOrderCertificate_of_smoothDivisor_cover {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData}
    (U : ∀ z : ↥W, z ∈ Z.support → W.Opens)
    (hU : ∀ (z : ↥W) (hz : z ∈ Z.support), z ∈ U z hz)
    (H : ∀ (z : ↥W) (hz : z ∈ Z.support), (U z hz).toScheme.IdealSheafData)
    (hH : ∀ (z : ↥W) (hz : z ∈ Z.support), IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (hZH : ∀ (z : ↥W) (hz : z ∈ Z.support),
      (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (J : ∀ (z : ↥W) (hz : z ∈ Z.support), Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ (z : ↥W) (hz : z ∈ Z.support), J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
    (hJcomp : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → ∀ x : ↥(H z hz).subscheme,
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V₀ : (H z hz).subscheme.Opens, x ∈ V₀ ∧
          Jz.comap V₀.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V₀.ι)
    (ih : ∀ (z : ↥W) (hz : z ∈ Z.support) (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      IsPrincipalizationCertificateOnOpens (H z hz).subscheme ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz μ
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    IsOrderCertificateOnOpens W p N μ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ (y : ↥V), y ∈ (Z.comap f).support → f.base y ∈ Z.support := by
    intro y hy
    have h1 : y ∈ ((Z.comap f).support : Set ↥V) := hy
    rw [coe_support_comap] at h1
    exact h1
  refine OrderCertificate.descend (fun y hy => f ⁻¹ᵁ U (f.base y) (hsup y hy))
    (fun y hy => hU _ _)
    (fun y hy => (H (f.base y) (hsup y hy)).comap (f ∣_ U (f.base y) (hsup y hy)))
    (fun y hy => isSmoothDivisor_comap_morphismRestrict hin f (U (f.base y) (hsup y hy))
      (H (f.base y) (hsup y hy)) (hH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N
      (hNsubH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hZH _ _))
    (fun y hy => (J (f.base y) (hsup y hy)).map (fun Jz =>
      Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)))))
    ?_ ?_ ?_ ?_
  · intro y hy hnone
    have hJn : J (f.base y) (hsup y hy) = none := by
      cases hJ : J (f.base y) (hsup y hy) with
      | none => rfl
      | some Jz =>
          rw [hJ] at hnone
          simp at hnone
    exact isOpen_preimage_support_comap_morphismRestrict f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z
      (hJnone _ _ hJn)
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact nonzeroOnComponents_comap_comapSubscheme hin f (U (f.base y) (hsup y hy))
          (H (f.base y) (hsup y hy)) Jz (hJcomp _ _ Jz hJ)
  · intro y hy Jz' hsome x hx
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact exists_isOpen_comap_eq_comap_morphismRestrict f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) N Mem Jz
          (hJloc _ _ Jz hJ) x hx
  · intro y hy Jz' hsome
    cases hJ : J (f.base y) (hsup y hy) with
    | none =>
        rw [hJ] at hsome
        simp at hsome
    | some Jz =>
        rw [hJ] at hsome
        have hJz : Jz.comap (comapSubscheme (f ∣_ U (f.base y) (hsup y hy))
            (H (f.base y) (hsup y hy))) = Jz' := Option.some.inj hsome
        subst hJz
        exact principalizationCertificate_comapSubscheme_of_isOpenImmersion hin f (U (f.base y) (hsup y hy)) (H (f.base y) (hsup y hy)) Z μ Mem
          Jz (ih _ _ Jz hJ)

private theorem comapPrincipalizationCertificate_of_principalizationCertificate {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z :=
  PrincipalizationCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset h)
    (fun hm => comapPrincipalizationCertificate_of_two_le hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    (fun h => comapOrderCertificate_of_support_subset h)
    (fun hmu => comapOrderCertificate_of_two_le hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

private theorem comapOrderCertificate_of_orderCertificate {k : Type u} [Field k] (hin : OpenImmersionStability k)
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    IsOrderCertificateOnOpens W p N μ Mem Z :=
  OrderCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N μ Mem Z _ => IsOrderCertificateOnOpens W p N μ Mem Z)
    (fun h => comapPrincipalizationCertificate_of_support_subset h)
    (fun hm => comapPrincipalizationCertificate_of_two_le hm)
    (fun M N μ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N μ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    (fun h => comapOrderCertificate_of_support_subset h)
    (fun hmu => comapOrderCertificate_of_two_le hmu)
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

theorem PrincipalizationCertificate.comap_of_openImmersionStability {k : Type u} [Field k]
    (hin : OpenImmersionStability k) {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  comapPrincipalizationCertificate_of_principalizationCertificate hin h V f inferInstance

theorem OrderCertificate.comap_of_isOpenImmersion {k : Type u} [Field k]
    (hin : OpenImmersionStability k) {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    {V : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    OrderCertificate V (f ≫ p) (N.comap f) μ (f.base ⁻¹' Mem) (Z.comap f) :=
  comapOrderCertificate_of_orderCertificate hin h V f inferInstance

theorem OrderCertificate.restrict {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z)
    (hin : OpenImmersionStability k) (U : W.Opens) :
    OrderCertificate U.toScheme (U.ι ≫ p) (N.comap U.ι) μ (U.ι.base ⁻¹' Mem) (Z.comap U.ι) :=
  h.comap_of_isOpenImmersion hin U.ι

end FunctorialResolution.EmbeddedResolution
