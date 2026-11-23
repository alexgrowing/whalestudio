import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_preimage_eq_top {S : Scheme.{0}} (F : Type) [Field F] (gp : Sp F ⟶ S) [IsDominant gp]
    (W : S.Opens) (hW : (W : Set S).Nonempty) : gp ⁻¹ᵁ W = ⊤ := by
  obtain ⟨q, hq⟩ := gp.denseRange.exists_mem_open W.isOpen hW
  refine top_unique fun z _ => ?_
  have : z = q := Subsingleton.elim (α := PrimeSpectrum F) z q
  subst this
  exact hq

theorem genFib_appLE_injective {S : Scheme.{0}} [IsIntegral S] (F : Type) [Field F] (gp : Sp F ⟶ S)
    [IsDominant gp] (W : S.Opens) (e : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W) :
    Function.Injective (gp.appLE W ⊤ e).hom := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊥ := by rw [hr]; simp
  have h2 : S.basicOpen r = ⊥ := by
    by_contra hne
    have hne' : (S.basicOpen r : Set S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hne (by ext1; simpa using h)
    have h3 := genFib_preimage_eq_top F gp _ hne'
    have h4 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊤ := by
      rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen, h3]
      simp
    rw [h4] at h1
    have : (⊤ : (Sp F).Opens) ≠ ⊥ := by
      intro h
      have hm : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F) ∈ ((⊤ : (Sp F).Opens) : Set (Sp F)) := trivial
      rw [h] at hm
      exact hm
    exact this h1
  exact (basicOpen_eq_bot_iff r).mp h2

theorem genFib_pushout_inl_injective {A B C : CommRingCat.{0}} (φ : A ⟶ B) (ψ : A ⟶ C) (hφ : φ.hom.Flat)
    (hψ : Function.Injective ψ.hom) : Function.Injective (pushout.inl φ ψ).hom := by
  algebraize [φ.hom, ψ.hom]
  have h' : IsPushout φ ψ (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  have e := h'.inl_isoPushout_inv
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := C)) :=
    Algebra.TensorProduct.includeLeft_injective hψ
  intro x y hxy
  apply hinj
  have := congrArg (fun z => h'.isoPushout.inv.hom z) hxy
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at this
  exact this

theorem genFib_affine_injective {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F) (H : IsPullback a t f gp) [Flat f] [IsIntegral S] [IsDominant gp]
    {W : S.Opens} (hW : IsAffineOpen W) (hWne : (W : Set S).Nonempty) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ W) : Function.Injective (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom := by
  have hT : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W := (genFib_preimage_eq_top F gp W hWne).ge
  have hUY : a ⁻¹ᵁ V = a ⁻¹ᵁ V ⊓ t ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hT e hUY hW (isAffineOpen_top _) hV
  have hfac : a.appLE V (a ⁻¹ᵁ V) le_rfl = pushout.inl _ _ ≫ pushoutSection H hT e hUY := by
    exact (pushout.inl_desc _ _ _).symm
  rw [hfac, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (pushoutSection H hT e hUY)).1.comp
    (genFib_pushout_inl_injective _ _ (f.flat_appLE hW hV e) (genFib_appLE_injective F gp W hT))

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_app_injective : ∀ {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F), IsPullback a t f gp → Flat f → IsIntegral S → IsDominant gp →
    ∀ U : X.Opens, Function.Injective (a.app U).hom := by
  intro S X Y F _ f gp a t H hf hS hd U
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine X.IsSheaf.section_ext (s := x) (t := 0) fun z hz => ?_
  obtain ⟨W, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show f z ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hzV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show z ∈ U ⊓ f ⁻¹ᵁ W from ⟨hz, hzW⟩)
  have hVU : V ≤ U := hVle.trans inf_le_left
  have e : V ≤ f ⁻¹ᵁ W := hVle.trans inf_le_right
  refine ⟨V, hVU, hzV, ?_⟩
  rw [map_zero]
  apply genFib_affine_injective F f gp a t H hW ⟨f z, hzW⟩ hV e
  rw [map_zero, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply,
    hx, map_zero]

end GlobalTheory.Mum
