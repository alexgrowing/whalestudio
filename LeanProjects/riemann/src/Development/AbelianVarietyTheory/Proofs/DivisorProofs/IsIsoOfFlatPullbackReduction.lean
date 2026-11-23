import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

open CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.NilThickIso

theorem appTop_spMap_eq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) :
    (spMap π).appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom π ≫
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc]; simp

theorem surjective_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) : Function.Surjective (spMap π).appTop := by
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso _).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso _).2

theorem isNilpotent_ker_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hn : IsNilpotent (RingHom.ker π)) : IsNilpotent (RingHom.ker (spMap π).appTop.hom) := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp]
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hk : RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom.comp
      (CommRingCat.ofHom π).hom).comp e) = (RingHom.ker π).comap e := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    constructor
    · intro h
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom h
      simpa using this
    · intro h; simp [h]
  rw [hk, Ideal.zero_eq_bot, ← le_bot_iff]
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hn, Ideal.zero_eq_bot]
  intro x hx
  simp only [Ideal.mem_comap, Ideal.mem_bot] at hx ⊢
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    (by rw [map_zero]; exact hx)

theorem surjective_of_sub_mem_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (h : ∀ c : C, ∃ b : B, c - φ b ∈ I.map (algebraMap A C)) : Function.Surjective φ := by
  obtain ⟨n, hn⟩ := hI
  let N : Submodule A C := LinearMap.range φ.toLinearMap
  have h1 : (⊤ : Submodule A C) ≤ N ⊔ I • ⊤ := by
    intro c _
    obtain ⟨b, hb⟩ := h c
    have hm : c - φ b ∈ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    have := Submodule.add_mem_sup (LinearMap.mem_range_self φ.toLinearMap b) hm
    simpa using this
  have h2 : ∀ k : ℕ, (⊤ : Submodule A C) ≤ N ⊔ I ^ k • ⊤ := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])
    | succ k ih =>
      calc ⊤ ≤ N ⊔ I ^ k • ⊤ := ih
        _ ≤ N ⊔ I ^ k • (N ⊔ I • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (k + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  have h3 := h2 n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at h3
  intro c
  obtain ⟨b, hb⟩ := h3 (Submodule.mem_top (x := c))
  exact ⟨b, hb⟩

theorem injective_of_flat_of_ker_le_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Flat A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (hs : Function.Surjective φ) (h : ∀ b : B, φ b = 0 → b ∈ I.map (algebraMap A B)) :
    Function.Injective φ := by
  obtain ⟨n, hn⟩ := hI
  set K := LinearMap.ker φ.toLinearMap with hKdef
  let mB : I ⊗[A] B →ₗ[A] B := (TensorProduct.lid A B).toLinearMap ∘ₗ I.subtype.rTensor B
  let mC : I ⊗[A] C →ₗ[A] C := (TensorProduct.lid A C).toLinearMap ∘ₗ I.subtype.rTensor C
  have hmC : Function.Injective mC := (TensorProduct.lid A C).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hcomm : ∀ t, φ (mB t) = mC (φ.toLinearMap.lTensor I t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mB, mC]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hex := lTensor_exact I (LinearMap.exact_subtype_ker_map φ.toLinearMap) hs
  have hrange : ∀ b ∈ I • (⊤ : Submodule A B), ∃ t, mB t = b := by
    intro b hb
    refine Submodule.smul_induction_on (p := fun b ↦ ∃ t, mB t = b) hb ?_ ?_
    · intro a ha x _
      exact ⟨⟨a, ha⟩ ⊗ₜ x, by simp [mB]⟩
    · rintro x y ⟨t, rfl⟩ ⟨s, rfl⟩
      exact ⟨t + s, map_add _ _ _⟩
  have hK : ∀ s : I ⊗[A] K, mB (K.subtype.lTensor I s) ∈ I • K := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [mB, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, Submodule.subtype_apply]
      exact Submodule.smul_mem_smul a.2 x.2
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have hle : K ≤ I • K := by
    intro k hk
    have hk' : k ∈ I • (⊤ : Submodule A B) := by rw [Ideal.smul_top_eq_map]; exact h k hk
    obtain ⟨t, rfl⟩ := hrange k hk'
    have h0 : φ.toLinearMap.lTensor I t = 0 := hmC (by rw [← hcomm, map_zero]; exact hk)
    obtain ⟨s, rfl⟩ := (hex t).mp h0
    exact hK s
  have hle' : ∀ k : ℕ, K ≤ I ^ k • K := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih =>
      calc K ≤ I ^ k • K := ih
        _ ≤ I ^ k • (I • K) := Submodule.smul_mono le_rfl hle
        _ = I ^ (k + 1) • K := by rw [pow_succ, Submodule.mul_smul]
  have h3 := hle' n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul] at h3
  rw [injective_iff_map_eq_zero]
  intro b hb
  exact (Submodule.mem_bot A).mp (h3 hb)

theorem ring_step {A A₀ B C B₀ C₀ : CommRingCat.{0}} (ψ : A ⟶ A₀) (β : A ⟶ B) (ρ : A ⟶ C)
    (φ : B ⟶ C) (πB : B ⟶ B₀) (πC : C ⟶ C₀) (β₀ : A₀ ⟶ B₀) (ρ₀ : A₀ ⟶ C₀) (φ₀ : B₀ ⟶ C₀)
    (hψ : Function.Surjective ψ) (hn : IsNilpotent (RingHom.ker ψ.hom))
    (hB : IsPushout β ψ πB β₀) (hC : IsPushout ρ ψ πC ρ₀) (hflat : ρ.hom.Flat)
    (w : β ≫ φ = ρ) (w₀ : φ ≫ πC = πB ≫ φ₀) (hφ₀ : IsIso φ₀) : IsIso φ := by
  have hkB := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hB hψ
  have hkC := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hC hψ
  have hπB : Function.Surjective πB := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout hB, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨a, rfl⟩ := hψ y
      exact ⟨β a, congr($(hB.w).hom a)⟩
  have hφ₀ := ConcreteCategory.bijective_of_isIso φ₀
  have hw₀ (b : B) : πC (φ b) = φ₀ (πB b) := congr($(w₀).hom b)
  algebraize [β.hom, ρ.hom]
  let φA : B →ₐ[A] C := { φ.hom with commutes' := fun a ↦ congr($(w).hom a) }
  have hs : Function.Surjective φA := by
    refine surjective_of_sub_mem_map φA (RingHom.ker ψ.hom) hn fun c ↦ ?_
    obtain ⟨y, hy⟩ := hφ₀.2 (πC c)
    obtain ⟨b, rfl⟩ := hπB y
    refine ⟨b, ?_⟩
    have h0 : πC (c - φ b) = 0 := by rw [map_sub, hw₀, hy, sub_self]
    have h1 : c - φ b ∈ RingHom.ker πC.hom := h0
    rw [hkC] at h1
    exact h1
  have hi : Function.Injective φA := by
    refine injective_of_flat_of_ker_le_map φA (RingHom.ker ψ.hom) hn hs fun b hb ↦ ?_
    have h0 : πB b = 0 := hφ₀.1 (by rw [← hw₀, show φ b = 0 from hb, map_zero, map_zero])
    rw [← RingHom.mem_ker, hkB] at h0
    exact h0
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hi, hs⟩

theorem affine_case (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p] [IsAffine Y]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  have : IsAffine Y₀ := IsAffine.of_isPullback hY
  have : IsAffine X₀ := IsAffine.of_isIso f₀
  have : IsAffine X := GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker π) hn
    (CommRingCat.ofHom π) hπ rfl hX this
  have hψ := surjective_appTop_spMap π hπ
  have hψn := isNilpotent_ker_appTop_spMap π hn
  have hfl : (p.appTop).hom.Flat := HasRingHomProperty.iff_of_isAffine.mp ‹Flat p›
  have key : IsIso f.appTop := ring_step (spMap π).appTop q.appTop p.appTop f.appTop j.appTop i.appTop
    q₀.appTop p₀.appTop f₀.appTop hψ hψn (isPushout_appTop_of_isPullback hY)
    (isPushout_appTop_of_isPullback hX) hfl (by rw [← w]; simp) (by
      rw [← Scheme.Hom.comp_appTop, w₀, Scheme.Hom.comp_appTop]) ⟨⟨(inv f₀).appTop, by rw [← Scheme.Hom.comp_appTop]; simp, by rw [← Scheme.Hom.comp_appTop]; simp⟩⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop))))

theorem general (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    Y.affineCover (fun k ↦ ?_)
  change IsIso (pullback.snd f (Y.affineCover.f k))
  set u := Y.affineCover.f k
  have hU : IsPullback (pullback.snd j u) (pullback.fst j u ≫ q₀) (u ≫ q) (spMap π) :=
    (IsPullback.of_hasPullback j u).flip.paste_vert hY
  have hX' : IsPullback (pullback.snd i (pullback.fst f u)) (pullback.fst i (pullback.fst f u) ≫ p₀)
      (pullback.fst f u ≫ p) (spMap π) :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).flip.paste_vert hX
  have hP : IsPullback (pullback.fst i (pullback.fst f u))
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) (i ≫ f) u :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).paste_vert (IsPullback.of_hasPullback f u)
  have hP' : IsPullback (pullback.fst i (pullback.fst f u) ≫ f₀)
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) j u :=
    IsPullback.of_iso hP (Iso.refl _) (asIso f₀) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [w₀]) (by simp)
  exact affine_case R R₀ π hπ hn (pullback.fst f u ≫ p) (u ≫ q) _ _ _ _ hX' hU (pullback.snd f u)
    hP'.isoPullback.hom (by rw [← w, pullback.condition_assoc]) (by simp)

theorem isIso_of_flat_of_isIso_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  intro R R₀ _ _ π hπ hn X Y X₀ Y₀ i j hX hY hfl f f₀ w₀ hf₀
  have : IsIso f₀.left := (Over.forget _).map_isIso f₀
  have : IsIso f.left := general R R₀ π hπ hn X.hom Y.hom X₀.hom Y₀.hom i j hX hY f.left f₀.left
    (Over.w f) w₀
  have : IsIso ((Over.forget _).map f) := this
  exact isIso_of_reflects_iso f (Over.forget _)

end GlobalTheory.NilThickIso
