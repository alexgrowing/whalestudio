import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcNotAbelian

theorem isProper_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (p : Spec (CommRingCat.of K)) (hp : t p ∈ abLocus G) :
    IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Spec (CommRingCat.of K') := (default : PrimeSpectrum K')
  have : Nonempty (Spec (CommRingCat.of K')) := ⟨q⟩
  have h₁ : IsProper (pullback.snd G.hom (u ≫ t)) :=
    hp K' (u ≫ t) ⟨q, congrArg (fun z => t z) (Subsingleton.elim (u q) p)⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]; infer_instance
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩

open TorusToProper in

theorem subsingleton_of_mono (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  have h := splitTorus_hom_proper_trivial_field K X B f hf
  have e : ptFun K X (AddMonoidAlgebra K X) (univ K X) = ptFun K X (AddMonoidAlgebra K X) 1 := by
    rw [← cancel_mono f, h, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have e₂ := (ptFun_fst K X _ (univ K X)).symm.trans
    ((congrArg (fun z => z.left ≫ Rosenlicht.torusFst _ X) e).trans (ptFun_fst K X _ 1))
  have e₃ : charRing X _ (univ K X) = charRing X (AddMonoidAlgebra K X) 1 :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
  have key : ∀ a : X, (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra K X) = 1 := by
    intro a
    have := congrArg (fun φ => φ (AddMonoidAlgebra.single a 1)) e₃
    simp only [charRing_single] at this
    simpa [univ] using this
  exact ⟨fun a b => AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K)) ((key a).trans (key b).symm)⟩

theorem subsingleton_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (A : Type) [CommRing A] (hA : IsField A) (t : Spec (CommRingCat.of A) ⟶ S) (p : Spec (CommRingCat.of A))
    (hp : t p ∈ abLocus G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ (Over.pullback t).obj G) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  letI := hA.toField
  have : IsProper ((Over.pullback t).obj G).hom := isProper_fibre G hG A t p hp
  exact subsingleton_of_mono A X _ f hf

end ArcNotAbelian

open ArcNotAbelian in

theorem arcWit_mem_range_jK_of_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (x : Sp (PowerSeries k)), χ x ∈ Set.range Y.j → x ∈ Set.range (jK (PowerSeries k)) := by
  intro E _ _ _ H D l Xo c k _ bF a O _ β Y χ W x hx
  refine mem_range_jK x fun hX => ?_
  have h₁ : χ x ∈ abLocus Y.t.G := by
    obtain ⟨p, hp⟩ := hx
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    rw [← hp]
    exact hz
  have h₂ : x ∈ abLocus W.t.G := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 x).1 h₁
  have hmax : (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one, ← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hF : IsField (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1) ≤ x.asIdeal := by
    rw [zero_add, pow_one, Ideal.span_le, Set.singleton_subset_iff]; exact hX
  obtain ⟨p, hp⟩ : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick (PowerSeries k) (Ideal.span {PowerSeries.X}) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial (a.restrict β).D₀.X := (a.restrict β).nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

end GlobalTheory
