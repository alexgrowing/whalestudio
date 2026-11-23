import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CrossIdentity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIntegralRatios
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

theorem isDominant_of_flat {X Y : Scheme.{0}} [IsIntegral Y] (f : X ⟶ Y) [Flat f] [Nonempty X] : IsDominant f := by
  have h : genericPoint Y ∈ Set.range f :=
    (Flat.generalizingMap f).stableUnderGeneralization_range (genericPoint_specializes (f (Classical.arbitrary X)))
      ⟨_, rfl⟩
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.2 h)

theorem nonempty_pullback_generic {R : Type} [CommRing R] [IsDomain R] {T X : Scheme.{0}} (g : T ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat g] [Flat p] (t : T) :
    Nonempty ↥(pullback g (pullback.fst p (jK R))) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  have hs : jK R ξ ⤳ (g ≫ p) t := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  obtain ⟨b, hb⟩ := (Flat.generalizingMap (g ≫ p)).stableUnderGeneralization_range hs ⟨t, rfl⟩
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := jK R) (g b) ξ hb
  obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := pullback.fst p (jK R)) b y hy.symm
  exact ⟨z⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem GenericRel.point (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    {B : Type} [CommRing B] [Algebra R B] {g' : Spec (CommRingCat.of B) ⟶ G'.left}
    {g : Spec (CommRingCat.of B) ⟶ G.left} {jL : U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hB : IsAdicComplete (I.map (algebraMap R B)) B)
    (h₁ : g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₂ : g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₃ : ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL') (h₄ : ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL)
    (h₅ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g)
    {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left)
    (hr : r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g') : r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g := by
  have c : (ρ ≫ g) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
    rw [Category.assoc, h₂, ← h₁, ← Category.assoc, ← hr, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f₂, e₁, e₂⟩ : ∃ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left, f₂ ≫ pullback.fst G.hom (jK R) = ρ ≫ g ∧
      f₂ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [← e₁, ← Category.assoc]
  refine congrArg (· ≫ _) (GlobalTheory.hom_ext_of_integral_ratios hL R I D A G U
    (fun k σ => ∃ σ', AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ') (fun k hk σ₀ => ?_) Z _ _ ?_ fun z => ?_)
  · obtain ⟨c, σ', σ, h⟩ := (hE k hk).1 σ₀
    exact ⟨c, σ, h.1, h.2.1, σ', h.2.2⟩
  · rw [e₂, Category.assoc]
    exact congrArg (r ≫ ·) (Over.w Φ.hom)
  · obtain ⟨i, hi⟩ := exists_chart U.LG.isLB ((r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z)
    have hi' : (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' := by rw [hr]; exact h₃ (Set.mem_univ (ρ z))
    rw [Category.assoc, e₁]
    refine ⟨i, jL, hi, h₄ (Set.mem_univ (ρ z)), ?_⟩
    rintro k hk σ τ ⟨σ', hσ⟩ ⟨τ', hτ⟩
    have x := GlobalTheory.GenericIso.cross_identity R I hR D D' A A' G G' hG hG' U U' hD j B g' g jL jL' hB h₁ h₃ h₄ h₅ k σ τ σ' τ' hσ hτ Z ρ z
    rw [hw.2 k hk σ' σ hσ Z r z i jL' hi hi', hw.2 k hk τ' τ hτ Z r z i jL' hi hi', hr, _root_.mul_assoc,
      _root_.mul_assoc]
    exact congrArg _ ((mul_comm _ _).trans (x.symm.trans (mul_comm _ _)))

theorem GenericRel.comm (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    (a' : G' ⟶ G') (a : G ⟶ G) (ha : ∀ e, (Over.pullback (thick R I e)).map a' ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map a) :
    (Over.pullback (jK R)).map a' ≫ Φ.hom = Φ.hom ≫ (Over.pullback (jK R)).map a := by
  have := hR.1
  have := U'.smooth
  have := U.separated
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by rwa [zero_add, pow_one])
  let x : (thickObj R I 0 G').left := eSec (thickObj R I 0 G') (Classical.arbitrary (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
  obtain ⟨i₁, m₁⟩ := exists_chart U.LG.isLB ((fstG I 0 G).left ((j 0).hom.left x))
  obtain ⟨i₂, m₂⟩ := exists_chart U.LG.isLB (a.left ((fstG I 0 G).left ((j 0).hom.left x)))
  obtain ⟨i₁', m₁'⟩ := exists_chart U'.LG.isLB ((fstG I 0 G').left x)
  obtain ⟨i₂', m₂'⟩ := exists_chart U'.LG.isLB (a'.left ((fstG I 0 G').left x))
  obtain ⟨B, _, _, g', g, hB, -, hf, ⟨b, -⟩, h₁, h₂, h₃, h₄, h₅⟩ := CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x (U.LG.L.U i₁ ⊓ a.left ⁻¹ᵁ U.LG.L.U i₂)
    (U'.LG.L.U i₁' ⊓ a'.left ⁻¹ᵁ U'.LG.L.U i₂') ⟨m₁, m₂⟩ ⟨m₁', m₂'⟩
  have h₆ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' ≫ a'.left → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g ≫ a.left := by
    intro e Z ρ r hr
    have hr' : r ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ≫ a'.left := hr
    have c : (ρ ≫ g') ≫ G'.hom = (r ≫ pullback.snd G'.hom (thick R I e)) ≫ thick R I e := by
      rw [Category.assoc _ (pullback.snd _ _), ← pullback.condition, ← Category.assoc r, hr']
      simp only [Category.assoc, Over.w]
    obtain ⟨r₀, e₁, e₂⟩ : ∃ r₀ : Z ⟶ (thickObj R I e G').left, r₀ ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ∧
        r₀ ≫ pullback.snd G'.hom (thick R I e) = r ≫ pullback.snd G'.hom (thick R I e) :=
      ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain rfl : r = r₀ ≫ ((Over.pullback (thick R I e)).map a').left := by
      refine pullback.hom_ext ?_ ?_
      · rw [hr', Category.assoc, P, ← Category.assoc r₀, e₁, Category.assoc]
      · rw [← e₂, Category.assoc]
        exact congrArg (r₀ ≫ ·) (Over.w ((Over.pullback (thick R I e)).map a')).symm
    have e₃ := congrArg (· ≫ a.left) (h₅ e Z ρ r₀ e₁)
    have e₄ := congrArg (fun q => r₀ ≫ q.left ≫ pullback.fst G.hom (thick R I e)) (ha e)
    simp only [Over.comp_left, Category.assoc, P] at e₃ e₄ ⊢
    exact e₄.trans e₃
  have := (unifPre_genericFibre_surjective_appTop_and_isIntegral hL.globalFns R I D' A' G' U'.toUnifPre).2
  have := nonempty_pullback_generic g' G'.hom b
  have := isDominant_of_flat (pullback.snd g' (pullback.fst G'.hom (jK R)))
  have p₁ := hw.point hL hR hG hG' hE hB h₁ h₂ (fun y hy => (h₃ hy).1) (fun y hy => (h₄ hy).1) h₅
    (pullback.fst g' (pullback.fst G'.hom (jK R))) (pullback.snd g' (pullback.fst G'.hom (jK R)))
    pullback.condition.symm
  have p₂ := hw.point hL hR hG hG' hE (g' := g' ≫ a'.left) (g := g ≫ a.left) hB
    (by rw [Category.assoc, Over.w, h₁]) (by rw [Category.assoc, Over.w, h₂]) (fun y hy => (h₃ hy).2)
    (fun y hy => (h₄ hy).2) h₆ (pullback.fst g' (pullback.fst G'.hom (jK R)))
    (pullback.snd g' (pullback.fst G'.hom (jK R)) ≫ ((Over.pullback (jK R)).map a').left)
    (by rw [Category.assoc, P, ← Category.assoc, ← pullback.condition, Category.assoc])
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := pullback G'.hom (jK R))
    (pullback.snd G.hom (jK R)) ((Over.w _).trans (Over.w _).symm)
    (pullback.snd g' (pullback.fst G'.hom (jK R))) (pullback.hom_ext ?_ ?_))
  · have e₃ := congrArg (· ≫ a.left) p₁
    simp only [Over.comp_left, Category.assoc, P] at e₃ p₂ ⊢
    exact p₂.trans e₃.symm
  · rw [Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((Over.w _).trans (Over.w _).symm)

theorem GenericRel.one (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) :
    η[(Over.pullback (jK R)).obj G'] ≫ Φ.hom = η[(Over.pullback (jK R)).obj G] := by
  have h := hw.comm hL hR hI hG hG' hj hE 1 1 fun e => by
    have := (hj e).1
    rw [Functor.map_one, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  rw [Functor.map_one, Functor.map_one, MonObj.comp_one] at h
  have e := congrArg (η[(Over.pullback (jK R)).obj G'] ≫ ·) h
  simp only [← Category.assoc, MonObj.comp_one] at e
  simpa [Hom.one_def] using e

end GlobalTheory.GenericIso
