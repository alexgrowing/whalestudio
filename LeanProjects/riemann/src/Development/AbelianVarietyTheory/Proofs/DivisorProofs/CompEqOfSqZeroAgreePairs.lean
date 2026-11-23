import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAgree

open GlobalTheory.MulUnramified

variable {C C₀ : Type} [CommRing C] [CommRing C₀] (π : C →+* C₀)

lemma spMap_surjective (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) :
    Function.Surjective (spMap π) := by
  intro (p : PrimeSpectrum C)
  change p ∈ Set.range (PrimeSpectrum.comap π)
  rw [range_comap_of_surjective _ _ hπ, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  refine p.isPrime.mem_of_pow_mem 2 ?_
  have : a ^ 2 ∈ RingHom.ker π ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hsq, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  rw [this]
  exact zero_mem _

lemma preimage_eq_of_agree (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    (V : Y.left.Opens) : f.left ⁻¹ᵁ V = f'.left ⁻¹ᵁ V := by
  have hs : Surjective (spMap π) := ⟨spMap_surjective π hπ hsq⟩
  have hf : Surjective (pullback.fst X.hom (spMap π)) := inferInstance
  have e := congrArg (·.left) (h (Over.mk (pullback.snd X.hom (spMap π)))
    (Over.homMk (pullback.fst X.hom (spMap π)) pullback.condition))
  simp only [Over.comp_left, Over.homMk_left] at e
  exact preimage_eq _ hf.surj e V

noncomputable def alg (X : Over (Sp C)) (V : X.left.Opens) : C →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ X.hom.appLE ⊤ V le_top).hom

lemma fromSpec_over (X : Over (Sp C)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (alg X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of C))) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, alg, spMap, CommRingCat.ofHom_hom, Spec.map_comp]

lemma appLE_alg {X Y : Over (Sp C)} (f : X ⟶ Y) (V : Y.left.Opens) (V' : X.left.Opens)
    (hf : V' ≤ f.left ⁻¹ᵁ V) (c : C) : f.left.appLE V V' hf (alg Y V c) = alg X V' c := by
  simp only [alg, CommRingCat.hom_comp, RingHom.comp_apply]
  exact comp_appLE_apply f.left Y.hom (Over.w f) _ _ _ _ _ _ _

lemma sub_mem (hπ : Function.Surjective π) {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    {V : Y.left.Opens} (hV : IsAffineOpen V) {V' : X.left.Opens} (hV' : IsAffineOpen V')
    (hf : V' ≤ f.left ⁻¹ᵁ V) (hf' : V' ≤ f'.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    f.left.appLE V V' hf s - f'.left.appLE V V' hf' s ∈ (RingHom.ker π).map (alg X V') := by
  set J := (RingHom.ker π).map (alg X V')
  let q : Γ(X.left, V') →+* Γ(X.left, V') ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* Γ(X.left, V') ⧸ J :=
    (Ideal.quotientMap J (alg X V') Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp (alg X V') := by
    ext c
    have e : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk _ c :=
      (RingEquiv.symm_apply_eq _).mpr rfl
    simp only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.quotientMap_mk]
  let y : Over.mk ((Over.mk (spMap ψ)).hom ≫ spMap π) ⟶ X :=
    Over.homMk (spMap q ≫ hV'.fromSpec) (by
      rw [Category.assoc, fromSpec_over]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  have e := congrArg (·.left) (h (Over.mk (spMap ψ)) y)
  simp only [y, Over.comp_left, Over.homMk_left, Category.assoc] at e
  rw [← hV.SpecMap_appLE_fromSpec f.left hV' hf, ← hV.SpecMap_appLE_fromSpec f'.left hV' hf',
    ← Category.assoc, ← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at e
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact congr($e s)

lemma eq_on_map {B R : Type} [CommRing B] [CommRing R] (I : Ideal C) (hI : I ^ 2 = 0)
    (φB : C →+* B) (φR : C →+* R) (β β' : B →+* R) (hβ : β.comp φB = φR) (hβ' : β'.comp φB = φR)
    (hd : ∀ b, β b - β' b ∈ I.map φR) {x : B} (hx : x ∈ I.map φB) : β x = β' x := by
  have hJ : I.map φR * I.map φR = ⊥ := by
    rw [← Ideal.map_mul, ← pow_two, hI, Submodule.zero_eq_bot, Ideal.map_bot]
  suffices β x = β' x ∧ β x ∈ I.map φR from this.1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [← RingHom.comp_apply β, hβ, ← RingHom.comp_apply β', hβ']
    exact ⟨rfl, Ideal.mem_map_of_mem _ hc⟩
  | zero => simp
  | add x y _ _ hx hy => exact ⟨by rw [map_add, map_add, hx.1, hy.1], by rw [map_add]; exact add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, map_mul, map_mul, ← hx.1, ← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hJ]
      exact Ideal.mul_mem_mul (hd a) hx.2
    · rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx.2

end GlobalTheory.SqZeroAgree

namespace GlobalTheory

open MulUnramified SqZeroAgree in

theorem comp_eq_of_sqZero_agree : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G),
    (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') →
    ∀ (T : Over (Sp C)) (w w' : T ⟶ K),
    (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') →
    w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  intro C C₀ _ _ π hπ hsq K G g g' hg T w w' hw h'
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.left (w.left t))) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ g.left ⁻¹ᵁ V⟩ :=
    K.left.isBasis_affineOpens.exists_subset_of_mem_open (a := w.left t) (u := g.left ⁻¹ᵁ V) htV
      (TopologicalSpace.Opens.isOpen _)
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWV' : W ≤ w.left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t) (u := w.left ⁻¹ᵁ V') htV'
      (TopologicalSpace.Opens.isOpen _)
  have hV'V₂ : V' ≤ g'.left ⁻¹ᵁ V := preimage_eq_of_agree π hπ hsq hg V ▸ hV'V
  have hWV'₂ : W ≤ w'.left ⁻¹ᵁ V' := preimage_eq_of_agree π hπ hsq hw V' ▸ hWV'
  refine ⟨W, htW, ?_⟩
  have key : ∀ s, w.left.appLE V' W hWV' (g.left.appLE V V' hV'V s) =
      w.left.appLE V' W hWV' (g'.left.appLE V V' hV'V₂ s) := by
    intro s
    have hx := sub_mem π hπ hg hV hV' hV'V hV'V₂ s
    have e := eq_on_map (RingHom.ker π) hsq (alg K V') (alg T W) (w.left.appLE V' W hWV').hom
      (w'.left.appLE V' W hWV'₂).hom (RingHom.ext (appLE_alg w V' W hWV'))
      (RingHom.ext (appLE_alg w' V' W hWV'₂)) (sub_mem π hπ hw hV' hW hWV' hWV'₂) hx
    have e' : w'.left.appLE V' W hWV'₂ (g.left.appLE V V' hV'V s) =
        w'.left.appLE V' W hWV'₂ (g'.left.appLE V V' hV'V₂ s) := by
      rw [comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V hWV'₂),
        comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
      have hh : w'.left ≫ g.left = w'.left ≫ g'.left := by rw [← Over.comp_left, h', Over.comp_left]
      rw [appLE_congr hh V W _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
    simp only [map_sub] at e
    rw [← sub_eq_zero, ← sub_eq_zero.mpr e, e', sub_self, sub_zero]
  have fin : (w.left ≫ g.left).appLE V W (le_preimage_of_comp _ _ hV'V hWV') =
      (w.left ≫ g'.left).appLE V W (le_preimage_of_comp _ _ hV'V₂ hWV') := by
    ext s
    rw [← comp_appLE_apply _ _ rfl _ _ _ hV'V hWV', ← comp_appLE_apply _ _ rfl _ _ _ hV'V₂ hWV']
    exact key s
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec _ hW (le_preimage_of_comp _ _ hV'V hWV'), fin,
    hV.SpecMap_appLE_fromSpec _ hW]

end GlobalTheory
