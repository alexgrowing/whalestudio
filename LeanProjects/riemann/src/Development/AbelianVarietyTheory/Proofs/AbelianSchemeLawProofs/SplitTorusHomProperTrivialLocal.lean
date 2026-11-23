import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusLocal

theorem pullback_map_eq_one {S S' : Scheme.{0}} (p : S' ⟶ S) (X : Type) [AddCommGroup X]
    (B : Over S) [GrpObj B] (f : splitTorus S X ⟶ B) (hf : IsMonHom f)
    (h : ∀ g : splitTorus S' X ⟶ (Over.pullback p).obj B, IsMonHom g →
      g = toUnit _ ≫ η[(Over.pullback p).obj B]) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S S' p X
  have h1 : e.hom ≫ (Over.pullback p).map f = 1 := h _ inferInstance
  have h2 : (Over.pullback p).map (1 : splitTorus S X ⟶ B) = 1 := Functor.map_one _
  rw [← cancel_epi e.hom, h1, ← Hom.one_def, h2, MonObj.comp_one]

theorem eq_one_of_isNilpotent_maximalIdeal (A : Type) [CommRing A] [IsLocalRing A]
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of A))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  refine splitTorus_hom_eq_one_of_nilpotent A _ hA X B f hf (pullback_map_eq_one _ X B f hf ?_)
  intro g hg
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_field (A ⧸ IsLocalRing.maximalIdeal A) X _ g hg

theorem eq_zero_of_forall_mem_map_pow {A C : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Free A C] (x : C)
    (hx : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A C)) : x = 0 := by
  let b := Module.Free.chooseBasis A C
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top, Ideal.mem_iInf]
  intro n
  have := TorusNil.map_mem_map _ (b.coord i) (hx n)
  rw [Algebra.algebraMap_self, Ideal.map_id] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) this

open TorusNil in

theorem pt_ext_of_quotients {A C : Type} [CommRing A] [CommRing C] [Algebra A C] {N : Type}
    (I : N → Ideal C) (hI : ∀ x, (∀ i, x ∈ I i) → x = 0)
    {B : Over (Spec (CommRingCat.of A))} [IsSeparated B.hom] {a b : sp A C ⟶ B}
    (h : ∀ i, spm (Ideal.Quotient.mkₐ A (I i)) ≫ a = spm (Ideal.Quotient.mkₐ A (I i)) ≫ b) :
    a = b := by
  have : IsAffine (sp A C).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  have hinj : Function.Injective (equalizer.ι a b).left.appTop := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hb := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    apply hb.1
    refine Eq.trans (hI _ fun i => ?_) (map_zero _).symm
    have h1 : (spm (Ideal.Quotient.mkₐ A (I i))).left.appTop x = 0 := by
      rw [← equalizer.lift_ι _ (h i), Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        hx, map_zero]
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))) x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine h2.symm.trans ?_
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ I i))).hom h1).trans (map_zero _)
  have := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι a b).left, ← Over.comp_left, equalizer.condition, Over.comp_left]

end TorusLocal

open TorusNil TorusLocal in

theorem splitTorus_hom_proper_trivial_local (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsProper B.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  have hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map (toUnit _ ≫ η[B]) := by
    intro n
    set J := IsLocalRing.maximalIdeal A ^ (n + 1) with hJ
    refine pullback_map_eq_one _ X B f hf fun g hg => ?_
    have hJt : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
    have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
    have : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk J)))).obj B).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    refine eq_one_of_isNilpotent_maximalIdeal (A ⧸ J) ⟨n + 1, ?_⟩ X _ g hg
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]
    rfl
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A (AddMonoidAlgebra A X)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap A (AddMonoidAlgebra A X ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1)).map
          (algebraMap A (AddMonoidAlgebra A X)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of A X
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
