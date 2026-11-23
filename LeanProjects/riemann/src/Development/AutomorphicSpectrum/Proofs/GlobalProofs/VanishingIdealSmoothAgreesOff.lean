import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.SmoothPart

theorem radical_eq_of_isReduced {X : Scheme.{0}} (Z : X.IdealSheafData) [IsReduced Z.subscheme] :
    Z.radical = Z := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical Z)
  rw [Scheme.IdealSheafData.le_def]
  intro U x hx
  rw [Scheme.IdealSheafData.radical_ideal] at hx
  obtain ⟨n, hn⟩ := hx
  rw [← Z.ker_subschemeι_app U, RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem ideal_vanishingIdeal_congr {X : Scheme.{0}} (A B : Closeds X) (W : X.affineOpens)
    (h : ∀ x ∈ W.1, x ∈ A ↔ x ∈ B) :
    (Scheme.IdealSheafData.vanishingIdeal A).ideal W =
      (Scheme.IdealSheafData.vanishingIdeal B).ideal W := by
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal]
  congr 1
  ext p
  have hp : W.2.fromSpec p ∈ W.1 := by
    exact (IsAffineOpen.range_fromSpec (U := W.1) W.2).le (Set.mem_range_self p)
  exact h _ hp

theorem isIso_inclusion_of_eq {X : Scheme.{0}} {I J : X.IdealSheafData} (h : I ≤ J) (e : I = J) :
    IsIso (Scheme.IdealSheafData.inclusion h) := by
  subst e
  rw [Scheme.IdealSheafData.inclusion_id]
  infer_instance

theorem exists_isOpenImmersion_of_comap_eq {X : Scheme.{0}} (I J : X.IdealSheafData) (O : X.Opens)
    (hO : (I.support : Set X) ⊆ O) (e : I.comap O.ι = J.comap O.ι) :
    ∃ h : I.subscheme ⟶ J.subscheme, IsOpenImmersion h ∧ h ≫ J.subschemeι = I.subschemeι := by
  have hsurj : Function.Surjective (pullback.snd O.ι I.subschemeι) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    ext y
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    apply hO
    rw [← I.range_subschemeι]
    exact Set.mem_range_self y
  have : Epi (pullback.snd O.ι I.subschemeι).base := (TopCat.epi_iff_surjective _).2 hsurj
  have : IsIso (pullback.snd O.ι I.subschemeι) := IsOpenImmersion.isIso _
  have hincl : IsIso (Scheme.IdealSheafData.inclusion e.ge) := isIso_inclusion_of_eq _ e.symm
  refine ⟨inv (pullback.snd O.ι I.subschemeι) ≫ (I.comapIso O.ι).inv ≫
    Scheme.IdealSheafData.inclusion e.ge ≫ (J.comapIso O.ι).hom ≫ pullback.snd _ _,
    inferInstance, ?_⟩
  simp only [Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    Scheme.IdealSheafData.inclusion_subschemeι_assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullback.condition,
    IsIso.inv_hom_id_assoc]

theorem smooth_and_comap_eq : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData)
    (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support →
    (O : Set X) = ((Z.support : Set X) \ A)ᶜ →
    Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧
      (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
  intro k _ X g Z A O hs hA hO
  have hred : IsReduced Z.subscheme := GlobalTheory.isReduced_of_smooth_of_isReduced (Z.subschemeι ≫ g)
  have hZ : Scheme.IdealSheafData.vanishingIdeal Z.support = Z := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_of_isReduced]
  have hAO : ∀ x, x ∈ O → (x ∈ A ↔ x ∈ Z.support) := by
    intro x hx
    have hx' : x ∈ (O : Set X) := hx
    rw [hO] at hx'
    refine ⟨fun h => hA h, fun h => ?_⟩
    by_contra hn
    exact hx' ⟨h, hn⟩
  have key : ∀ W : X.affineOpens, W.1 ≤ O →
      (Scheme.IdealSheafData.vanishingIdeal A).ideal W = Z.ideal W := by
    intro W hW
    rw [ideal_vanishingIdeal_congr A Z.support W (fun x hx => hAO x (hW hx)), hZ]
  have hcomap : (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      key _ (Scheme.Opens.ι_image_le O U.1)]
  refine ⟨?_, hcomap⟩
  have hsub : (((Scheme.IdealSheafData.vanishingIdeal A).support : Closeds X) : Set X) ⊆ O := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hO]
    exact fun x hx hx' => hx'.2 hx
  obtain ⟨h, hh, hc⟩ := exists_isOpenImmersion_of_comap_eq _ Z O hsub hcomap
  rw [← hc, Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.SmoothPart
