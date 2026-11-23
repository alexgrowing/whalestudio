import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem lb_descends_fg : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp k) (p : X ⟶ Sp V) (φ : X ⟶ X₀), QuasiCompact p₀ → IsSeparated p₀ → IsPullback φ p p₀ (spMap (algebraMap k V)) → ∀ L : LB X, L.IsLB → ∃ R : Subalgebra k V, R.FG ∧ ∃ M : LB (pullback p₀ (spMap (algebraMap k R))), M.IsLB ∧ ∀ σ : X ⟶ pullback p₀ (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = φ → σ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom → LBIso L (M.pull σ) := by
  intro k V _ _ _ X₀ X p₀ p φ hqc hsep hpb L hL
  haveI := hqc
  haveI := hsep
  have hcompS : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
      (g : B →+* C), spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    simp only [spMap, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp]
  obtain ⟨R₀, ι₀, hι₀c, hR₀⟩ : ∃ (R₀ : Subring V) (ι₀ : k →+* R₀),
      R₀.subtype.comp ι₀ = algebraMap k V ∧ ∀ x ∈ R₀, ∃ a, algebraMap k V a = x :=
    ⟨(algebraMap k V).range, (algebraMap k V).rangeRestrict, by ext a; rfl,
      fun x hx => RingHom.mem_range.mp hx⟩
  haveI : QuasiSeparated p₀ := inferInstance
  haveI : QuasiCompact (pullback.snd p₀ (spMap ι₀)) := inferInstance
  haveI : QuasiSeparated (pullback.snd p₀ (spMap ι₀)) := inferInstance
  have hw0 : φ ≫ p₀ = (p ≫ spMap R₀.subtype) ≫ spMap ι₀ := by
    rw [Category.assoc, ← hcompS, hι₀c]; exact hpb.w
  obtain ⟨π, hπ1, hπ2⟩ : ∃ π : X ⟶ pullback p₀ (spMap ι₀),
      π ≫ pullback.fst _ _ = φ ∧ π ≫ pullback.snd _ _ = p ≫ spMap R₀.subtype :=
    ⟨pullback.lift φ _ hw0, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hright : IsPullback (pullback.fst p₀ (spMap ι₀)) (pullback.snd p₀ (spMap ι₀)) p₀
      (spMap ι₀) := IsPullback.of_hasPullback _ _
  have hleft : IsPullback π p (pullback.snd p₀ (spMap ι₀)) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ hπ2 hright
    rw [hπ1, ← hcompS, hι₀c]; exact hpb
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring V R₀ X (pullback p₀ (spMap ι₀)) p
    (pullback.snd p₀ (spMap ι₀)) π L hleft hL
  obtain ⟨R, hRfg, hSR⟩ : ∃ R : Subalgebra k V, R.FG ∧ (S : Set V) ⊆ R :=
    ⟨_, Subalgebra.fg_adjoin_finset S, Algebra.subset_adjoin⟩
  refine ⟨R, hRfg, ?_⟩
  have h : R₀ ≤ R.toSubring := by
    intro x hx
    obtain ⟨a, rfl⟩ := hR₀ x hx
    exact R.algebraMap_mem a
  have hcR : R.val.toRingHom.comp (algebraMap k R) = algebraMap k V := by
    ext a; rfl
  have hw1 : φ ≫ p₀ = (p ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, ← hcompS, hcR]; exact hpb.w
  have hinc : (Subring.inclusion h).comp ι₀ = (algebraMap k R : k →+* R) := by
    ext a
    have := RingHom.congr_fun hι₀c a
    simpa using this
  have hw2 : pullback.fst p₀ (spMap (algebraMap k R)) ≫ p₀ =
      (pullback.snd p₀ (spMap (algebraMap k R)) ≫ spMap (Subring.inclusion h)) ≫
        spMap ι₀ := by
    rw [Category.assoc, ← hcompS, hinc]; exact pullback.condition
  obtain ⟨π₁, hπ₁1, hπ₁2⟩ : ∃ π₁ : pullback p₀ (spMap (algebraMap k R)) ⟶ pullback p₀ (spMap ι₀),
      π₁ ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π₁ ≫ pullback.snd _ _ =
        pullback.snd p₀ (spMap (algebraMap k R)) ≫ spMap (Subring.inclusion h) :=
    ⟨pullback.lift _ _ hw2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb1 : IsPullback π₁ (pullback.snd p₀ (spMap (algebraMap k R)))
      (pullback.snd p₀ (spMap ι₀)) (spMap (Subring.inclusion h)) := by
    refine IsPullback.of_right ?_ hπ₁2 hright
    rw [hπ₁1, ← hcompS, hinc]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨σ₀, hσ₀1, hσ₀2⟩ : ∃ σ₀ : X ⟶ pullback p₀ (spMap (algebraMap k R)),
      σ₀ ≫ pullback.fst _ _ = φ ∧ σ₀ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom :=
    ⟨pullback.lift φ _ hw1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsub : spMap R.val.toRingHom ≫ spMap (Subring.inclusion h) = spMap R₀.subtype := by
    rw [← hcompS]
    exact congrArg spMap (RingHom.ext fun x => rfl)
  have hj1 : σ₀ ≫ π₁ = π := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπ₁1, hσ₀1, hπ1]
    · rw [Category.assoc, hπ₁2, ← Category.assoc, hσ₀2, Category.assoc, hsub, hπ2]
  obtain ⟨M, hM, hLM⟩ := hS R.toSubring h hSR _ _ π₁ σ₀ hpb1 hj1 hσ₀2
  refine ⟨M, hM, fun σ h1 h2 => ?_⟩
  have hσ : σ = σ₀ := pullback.hom_ext (h1.trans hσ₀1.symm) (h2.trans hσ₀2.symm)
  subst hσ
  exact hLM

end GlobalTheory.CompanionTheory.Ar.Approx
