import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.ToricTorsionRankBounds

theorem card_toric_torsion (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (N : ℕ) (hN : (N : k) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
      N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  have hk := E.isKernel
  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X
  obtain ⟨-, hcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e N hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  rw [← hcard]
  refine (Nat.card_eq_of_bijective
    (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
  · intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · rintro ⟨x, hx, t, rfl⟩
    have hx₁ : i t ^ N = 1 := hx
    exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩

theorem bound_algClosed (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (g N : ℕ) (hG : IsSemiAbelian G) (hg : SmoothOfRelativeDimension g G.hom)
    (hN : (N : k) ≠ 0) (m : ℕ) (P : Fin m → (𝟙_ (Over (Sp k)) ⟶ G)) (hP : Function.Injective P)
    (hP' : ∀ i, P i ^ N = 1) :
    m * N ^ @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ ≤ N ^ (2 * g) := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have h := GlobalTheory.card_torsion_mul_card_toric_torsion k G E g N hG hg hN
  rw [card_toric_torsion k G E N hN] at h
  have hne : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact pow_ne_zero _ hN0 h.symm
  haveI := Nat.finite_of_card_ne_zero hne
  have hm : m ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} := by
    have := Nat.card_le_card_of_injective
      (fun i : Fin m => (⟨P i, hP' i⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1}))
      (fun a b hab => hP (congrArg Subtype.val hab))
    simpa using this
  rw [← h]
  exact Nat.mul_le_mul_right _ hm

end PositivityTheory.Xgn.ToricTorsionRankBounds

theorem PositivityTheory.Xgn.two_torsion_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) := by
  intro S G _ hG g hg k _ h2 x Gk _ ψ hψ τ m Q hQ hQ2
  let Ω := AlgebraicClosure k
  let f : Sp Ω ⟶ Sp k := spMap (algebraMap k Ω)
  haveI : Flat f := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  haveI : Surjective f := ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  haveI : Epi f := Flat.epi_of_flat_of_surjective f
  have hp := isGrpPullback_pullback G (f ≫ x)
  obtain ⟨e, he, -⟩ := grpPullback_iso ((isGrpPullback_pullback Gk f).comp hψ) hp
  haveI := he
  let E : TorusExtension ((Over.pullback (f ≫ x)).obj G) :=
    torusExtOfIso e (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC f τ)
  have hg' : SmoothOfRelativeDimension g ((Over.pullback (f ≫ x)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h2' : ((2 : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (map_ne_zero _).2 h2
  have hinj : Function.Injective (pushHom hp (𝟙_ (Over (Sp Ω)))) := by
    intro a b hab
    have e : a.left ≫ pullback.fst G.hom (f ≫ x) = b.left ≫ pullback.fst G.hom (f ≫ x) :=
      congrArg (fun z => z.left) hab
    exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w a).trans (Over.w b).symm))
  let U : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ f ≫ x) ⟶ Over.mk x :=
    Over.homMk f (Category.id_comp (f ≫ x)).symm
  let P : Fin m → (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback (f ≫ x)).obj G) := fun i =>
    Over.homMk (hp.1.lift (U ≫ Q i).left (𝟙_ (Over (Sp Ω))).hom (Over.w (U ≫ Q i))) (hp.1.lift_snd _ _ _)
  have hP : ∀ i, pushHom hp (𝟙_ (Over (Sp Ω))) (P i) = preHom U (Q i) := fun i =>
    Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  refine PositivityTheory.Xgn.ToricTorsionRankBounds.bound_algClosed Ω _ E g 2 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f ≫ x) G hG) hg' h2' m P ?_ ?_
  · intro a b hab
    have h1 : preHom U (Q a) = preHom U (Q b) := by rw [← hP, ← hP, hab]
    have h3 : f ≫ (Q a).left = f ≫ (Q b).left := congrArg (fun z => z.left) h1
    exact hQ (Over.OverMorphism.ext ((cancel_epi f).1 h3))
  · intro i
    apply hinj
    rw [map_pow, hP, ← map_pow, hQ2, map_one, map_one]
