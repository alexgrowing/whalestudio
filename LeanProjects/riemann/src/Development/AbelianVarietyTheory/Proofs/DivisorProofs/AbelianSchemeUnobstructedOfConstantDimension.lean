import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimRed

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev qmap (π : R →+* R₀) (f : R) : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f} :=
  Ideal.quotientMap _ π (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap]; exact Ideal.mem_span_singleton_self _)))

theorem qmap_facts (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) (f : R) :
    Function.Surjective (qmap π f) ∧ RingHom.ker (qmap π f) = I.map (Ideal.Quotient.mk _) ∧
      (I.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ 2 = 0 ∧
      (qmap π f).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π := by
  refine ⟨Ideal.quotientMap_surjective hπ, ?_, ?_, Ideal.quotientMap_comp_mk _⟩
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨r, rfl⟩ := hπ c
      refine ⟨x - r * f, ?_, ?_⟩
      · rw [← hk, RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
      · rw [Ideal.Quotient.eq]
        simpa using Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self f)
    · rintro ⟨y, hy, hyx⟩
      rw [Ideal.Quotient.eq] at hyx
      have h1 : π (y - x) ∈ Ideal.span {π f} := by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyx
        rw [← hc, map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have h2 : π y = 0 := by rw [← RingHom.mem_ker, hk]; exact hy
      rw [map_sub, h2, zero_sub] at h1
      simpa using (Ideal.span {π f}).neg_mem h1
  · rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot]; exact Ideal.zero_eq_bot.symm

theorem smooth_paste {X Y Z S T : Scheme.{0}} (p : X ⟶ S) (u : Y ⟶ S) (v : Z ⟶ Y) (w : T ⟶ S) (d : Z ⟶ T)
    (hw : d ≫ w = v ≫ u) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd p w)) :
    SmoothOfRelativeDimension g (pullback.snd (pullback.snd p u) v) := by
  have outer := (IsPullback.of_hasPullback (pullback.snd p u) v).paste_horiz (IsPullback.of_hasPullback p u)
  rw [← hw] at outer
  have sq := IsPullback.of_right
    (h₁₁ := pullback.lift (pullback.fst (pullback.snd p u) v ≫ pullback.fst p u)
      (pullback.snd (pullback.snd p u) v ≫ d) (by rw [Category.assoc]; exact outer.w))
    (by rw [pullback.lift_fst]; exact outer) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p w)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h

theorem smooth_zero_of_subsingleton [Subsingleton R₀] {X : Scheme.{0}} (p : X ⟶ Sp R₀) :
    SmoothOfRelativeDimension 0 p :=
  ⟨fun x ↦ absurd (Subsingleton.elim (⊤ : Ideal R₀) (p x).asIdeal) (p x).isPrime.ne_top.symm⟩

theorem lift_of_split (hU : UnobDim) (n : ℕ) : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ e : Fin n → R₀, CompleteOrthogonalIdempotents e →
    (∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g
      (pullback.snd A₀.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k}))))) →
    ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  induction n with
  | zero =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he _
    have h01 : (0 : R₀) = 1 := by simpa using he.complete
    haveI : Subsingleton R₀ := subsingleton_of_zero_eq_one h01
    exact hU R I hI R₀ π hπ hk A₀ 0 hA (smooth_zero_of_subsingleton _)
  | succ n ih =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he hsm
    have hnil : ∀ x ∈ RingHom.ker π, IsNilpotent x := fun x hx ↦ ⟨2, by
      rw [hk] at hx
      have h2 := Ideal.pow_mem_pow hx 2
      rw [hI] at h2
      simpa using h2⟩
    obtain ⟨ε, hε, hπε⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hnil (e 0) (hπ _) (he.idem 0)
    refine GlobalTheory.T.exists_abelianScheme_lift_of_splitRing R R₀ I hI π hπ hk ε hε A₀ hA ?_
    intro f hf
    obtain ⟨hρs, hρk, hρ2, hρc⟩ := qmap_facts I hI π hπ hk f
    let B : Over (Sp (R₀ ⧸ Ideal.span {π f})) := (Over.pullback (spMap (Ideal.Quotient.mk _))).obj A₀
    letI : GrpObj B := Functor.grpObjObj
    have hB : IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) (pullback.fst _ _) := isGrpPullback_pullback A₀ _
    have hBa : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hB
    suffices H : ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (i : B.left ⟶ A.left),
        IsGrpPullback B A (spMap (qmap π f)) i ∧ IsAbelianScheme A by
      obtain ⟨A, _, i, h1, h2⟩ := H
      exact ⟨A, _, B, _, i, pullback.fst _ _, qmap π f, hρc, h1, hB, h2⟩
    rcases hf with rfl | rfl
    · have hm := he.map (Ideal.Quotient.mk (Ideal.span {π f}))
      refine ih (R ⧸ Ideal.span {f}) (I.map (Ideal.Quotient.mk _)) hρ2 (R₀ ⧸ Ideal.span {π f}) (qmap π f) hρs hρk
        B hBa (fun k ↦ Ideal.Quotient.mk _ (e k.succ)) ⟨⟨fun k ↦ hm.idem k.succ,
          fun i j hij ↦ hm.ortho ((Fin.succ_injective _).ne hij)⟩, ?_⟩ ?_
      · have hc := hm.complete
        rw [Fin.sum_univ_succ] at hc
        have h0 : Ideal.Quotient.mk (Ideal.span {π f}) (e 0) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, ← hπε]; exact Ideal.mem_span_singleton_self _
        simpa [h0] using hc
      · intro k
        obtain ⟨g, hg⟩ := hsm k.succ
        refine ⟨g, smooth_paste A₀.hom _ _ _
          (spMap (Ideal.Quotient.lift (Ideal.span {1 - e k.succ})
            ((Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)})).comp
              (Ideal.Quotient.mk (Ideal.span {π f}))) ?_)) ?_ g hg⟩
        · intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          have h0 : (Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)}))
              (Ideal.Quotient.mk (Ideal.span {π f}) (1 - e k.succ)) = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact Ideal.mem_span_singleton_self _
          rw [RingHom.comp_apply, map_mul, map_mul, h0, mul_zero]
        · rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
    · obtain ⟨g, hg⟩ := hsm 0
      have h1 : π (1 - ε) = 1 - e 0 := by rw [map_sub, map_one, hπε]
      rw [← h1] at hg
      exact hU _ _ hρ2 _ _ hρs hρk B g hBa hg

theorem abelianUnobstructed_of_unobDim : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  intro hU R _ I hI R₀ _ π hπ hk A₀ _ hA
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension R₀ A₀ hA
  exact lift_of_split hU n R I hI R₀ π hπ hk A₀ hA e he hsm

end GlobalTheory.DimRed
