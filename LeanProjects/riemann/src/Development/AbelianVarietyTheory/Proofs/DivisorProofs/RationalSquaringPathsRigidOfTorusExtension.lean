import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZeroStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.TorExt

theorem algebraMap_comp_C (Ω : Type) [Field Ω] :
    (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp RatFunc.C =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp PowerSeries.C := by
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply]
  rw [← RatFunc.algebraMap_C]
  have := RatFunc.coe_coe (Polynomial.C c)
  simp only [Polynomial.coe_C] at this
  exact this.symm

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    unitSec G ≫ f.left = unitSec H := by
  rw [unitSec, unitSec, sec, sec, ← Over.comp_left, IsMonHom.one_hom]

theorem isLocalHom_field {K L : Type} [Field K] [Field L] (φ : K →+* L) : IsLocalHom φ :=
  ⟨fun x hx => by
    by_cases h : x = 0
    · subst h; simp at hx
    · exact IsUnit.mk0 x h⟩

theorem exists_lift {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) {Z : Scheme.{0}}
    (z : Z ⟶ Sp Ω) (f : Z ⟶ G.left) (hf : f ≫ G.hom = z) (hq : letI := E.grpB; f ≫ E.q.left = z ≫ unitSec E.B) :
    letI := E.addCommGroup
    ∃ g : Z ⟶ (splitTorus (Sp Ω) E.X).left, g ≫ E.i.left = f ∧ g ≫ (splitTorus (Sp Ω) E.X).hom = z := by
  letI := E.addCommGroup
  letI := E.grpB
  let f' : Over.mk z ⟶ G := Over.homMk f hf
  have h : f' ≫ E.q = toUnit _ ≫ η := by
    ext
    simp [f', hq, unitSec, sec]
  refine ⟨(E.isKernel.lift f' (toUnit _) h).left, ?_, ?_⟩
  · rw [← Over.comp_left, E.isKernel.lift_fst]
    rfl
  · exact Over.w (E.isKernel.lift f' (toUnit _) h)

theorem mono_i {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup
    Mono E.i.left := by
  letI := E.addCommGroup
  letI := E.grpB
  have : Mono E.i := ⟨fun a b hab => E.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  exact Over.mono_left_of_mono _

end GlobalTheory.Nef.TorExt

namespace GlobalTheory.Nef

open TorExt in

theorem ratRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G],
    Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  intro Ω _ _ G _ ⟨E⟩ ξ hξ ⟨β, hβ⟩
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI := mono_i E
  haveI := isLocalHom_field (algebraMap (RatFunc Ω) (LaurentSeries Ω))
  obtain ⟨-, bc2⟩ := GlobalTheory.T.formalSquaringPaths_baseChange_and_hom
  obtain ⟨epi1, -⟩ := GlobalTheory.T.spec_injectiveRingMap_cancellation
  set T := splitTorus (Sp Ω) E.X
  set a := algebraMap (RatFunc Ω) (LaurentSeries Ω)
  set ι₀ := algebraMap (PowerSeries Ω) (LaurentSeries Ω)
  have ha : Function.Injective a := a.injective
  have hC : spMap a ≫ spMap RatFunc.C = spMap ι₀ ≫ spMap (PowerSeries.C (R := Ω)) := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, algebraMap_comp_C]
  have hq : ξ ≫ E.q.left = spMap (PowerSeries.C (R := Ω)) ≫ unitSec E.B := by
    have := GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero Ω E.B inferInstance (ξ ≫ E.q.left) ((bc2 _ G E.B E.q Ω 2 (𝟙 _) ξ).1 hξ)
      ⟨β ≫ E.q.left, by rw [← Category.assoc, hβ, Category.assoc]⟩
    rw [this, triv, Category.id_comp]
  have hbase : ξ ≫ G.hom = spMap (PowerSeries.C (R := Ω)) := by
    rw [hξ.base, Category.comp_id]
  obtain ⟨ζ, hζ, hζT⟩ := exists_lift E _ ξ hbase hq
  have hβG : β ≫ G.hom = spMap (RatFunc.C (K := Ω)) :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hbase, hC])
  have hβq : β ≫ E.q.left = spMap (RatFunc.C (K := Ω)) ≫ unitSec E.B :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hq, reassoc_of% hC])
  obtain ⟨βT, hβT, -⟩ := exists_lift E _ β hβG hβq
  have hTunit : unitSec T ≫ E.i.left = unitSec G := unitSec_comp E.i
  have hpath : IsPath T 2 (𝟙 _) ζ := by
    refine ⟨by rw [hζT, Category.comp_id], ?_, ?_⟩
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.zero, Category.assoc, hTunit]
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.scale, Category.assoc,
        (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.2, reassoc_of% hζ]
  have hrat : IsRatPath ζ :=
    ⟨βT, by rw [← cancel_mono E.i.left, Category.assoc, hβT, hβ, Category.assoc, hζ]⟩
  have h := GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero Ω E.X ζ hpath hrat
  rw [← hζ, h, (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.1]

end GlobalTheory.Nef
