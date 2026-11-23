import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh

set_option autoImplicit false

namespace GlobalTheory.CxCoh.AlgDict

universe u

variable {R : Type} [CommRing R] {C : Type u} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem singleComplex_mem_cocyclesOne_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T1) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z1 ↔ c.1 ∈ Z1 F := by
  change (Cx.single (Coef.ofAlg F)).D1 c = 0 ↔ _
  constructor
  · intro h T T' T'' φ ψ
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0 at this
    linear_combination -this
  · intro h
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext T T' T'' φ ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
    rw [h φ ψ]; ring

theorem singleComplex_mem_cocyclesTwo_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T2) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z2 ↔ c.1 ∈ Z2 F :=
  ⟨fun h _ _ _ _ φ ψ χ ↦ h.1 _ _ _ _ φ ψ χ,
    fun h ↦ ⟨fun _ _ _ _ φ ψ χ ↦ h φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _,
      fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩

variable {C' : Type u} [Category.{0} C'] (G : C' ⥤ C)

theorem h1_injective (hi : Function.Injective (CoefMap.restrict F G).pull1) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z1 F := (singleComplex_mem_cocyclesOne_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull1 (H1.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    exact ⟨g, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H1.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨g', Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h1_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull1) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z1 (G ⋙ F) := (singleComplex_mem_cocyclesOne_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H1.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ ↦ 0), (singleComplex_mem_cocyclesOne_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨-g, Prod.ext ?_ (Subsingleton.elim _ _)⟩
  rw [map_neg]
  funext T T' φ
  have := congrFun (congrFun (congrFun hg T) T') φ
  change -(d0 (G ⋙ F) g T T' φ) = -(f.1 _ _ (G.map φ)) + z'.1.1 T T' φ
  rw [this]
  change -((f.1 _ _ (G.map φ)) - z'.1.1 T T' φ) = _
  abel

theorem h2_injective (hi : Function.Injective (CoefMap.restrict F G).pull2) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z2 F := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull2 (H2.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull2 0 := by
    rw [map_zero, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    exact ⟨g.1, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H2.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨(g', fun _ ↦ 0), Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h2_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull2) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z2 (G ⋙ F) := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H2.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ _ _ ↦ 0, fun _ ↦ 0), (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨(-g, fun _ ↦ 0), Prod.ext ?_ (Subsingleton.elim _ _)⟩
  funext T T' T'' φ ψ
  have := congrFun (congrFun (congrFun (congrFun (congrFun hg T) T') T'') φ) ψ
  change d1 (G ⋙ F) (-g) T T' T'' φ ψ = -(f.1 _ _ _ (G.map φ) (G.map ψ)) + z'.1.1 T T' T'' φ ψ
  rw [map_neg, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, this]
  change -((f.1 _ _ _ (G.map φ) (G.map ψ)) - z'.1.1 T T' T'' φ ψ) = _
  abel

end GlobalTheory.CxCoh.AlgDict

theorem GlobalTheory.CxCoh.single_algebra_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C),
    Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 →
    ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo :=
  fun _ _ _ _ _ _ F G h1 h2 ↦
    ⟨⟨AlgDict.h1_injective F G h1.1, AlgDict.h1_surjective F G h1.2⟩,
      AlgDict.h2_injective F G h2.1, AlgDict.h2_surjective F G h2.2⟩
