import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneNonproperPowerSeries
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

noncomputable section

namespace GlobalTheory.PullCalcTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem all_six : PullCubCompSt ∧ PullCubCancelSt ∧ SABCompSt ∧ SABCancelSt ∧ AbLocusOneSt ∧ ProjProperSt :=
  ⟨pullCubComp, pullCubCancel, sabComp pullCubComp, sabCancel pullCubCancel, abLocusOne, projProper⟩

section Cube

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

theorem base_eq (m : CubeMap G' G) : m.e = eSec G' ≫ m.F ≫ G.hom := by
  have a : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  rw [← Category.assoc, m.e_comm, Category.assoc, a]
  exact (Category.comp_id _).symm

theorem cubeMap_ext (m n : CubeMap G' G) (h : m.F = n.F) : m = n := by
  have h3 : m.F3 = n.F3 := hom_ext_triple _ fun i => by rw [cubeMap_comp_proj_three, cubeMap_comp_proj_three, h]
  have he : m.e = n.e := by rw [base_eq, base_eq, h]
  cases m; cases n
  simp only at h h3 he
  subst h h3 he
  rfl

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' S'' : Scheme.{0}}

theorem sabMap_ext {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m n : SABMap t' t f) (h : m.φ = n.φ) : m = n := by
  have := cubeMap_ext m.cm n.cm h
  cases m; cases n
  simp only at this
  subst this
  rfl

theorem existsUnique_cancel {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)) : ∃! m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n
  refine ⟨k, hk, fun k' hk' => sabMap_ext _ _ (m.cart.1.hom_ext (hk'.symm.trans hk) ?_)⟩
  exact k'.cart.1.w.trans k.cart.1.w.symm

end Triple

theorem abLocus_torus (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    IsSemiAbelian (splitTorus (Spec (CommRingCat.of k)) ℤ) ∧ abLocus (splitTorus (Spec (CommRingCat.of k)) ℤ) = ∅ := by
  refine ⟨GlobalTheory.Diag.isSemiAbelian _ ℤ, Set.eq_empty_of_forall_notMem fun s hs => ?_⟩
  have h := hs k (𝟙 _) ⟨s, rfl⟩
  refine GlobalTheory.MultiplicativeTorusSetting.not_isProper_torus (k := k) ?_
  have e : (splitTorus (Spec (CommRingCat.of k)) ℤ).hom =
      inv (pullback.fst (splitTorus (Spec (CommRingCat.of k)) ℤ).hom (𝟙 _)) ≫ pullback.snd _ (𝟙 _) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem not_isProjOver_affineLine (R : Type) [CommRing R] [Nontrivial R] :
    ¬ IsProjOver (spMap (Polynomial.C : R →+* Polynomial R)) := fun h => by
  have hp := projProper R _ _ h
  have hf : IsFinite (spMap (Polynomial.C : R →+* Polynomial R)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨hp, inferInstance⟩
  have h2 := (IsFinite.SpecMap_iff _).1 hf
  exact Polynomial.not_finite (R := R) (RingHom.finite_algebraMap.1 h2)

end GlobalTheory.PullCalcTest
