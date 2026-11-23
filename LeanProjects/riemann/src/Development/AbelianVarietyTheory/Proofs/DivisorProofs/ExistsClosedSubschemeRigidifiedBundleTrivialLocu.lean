import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidifiedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocusLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in

theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} (N : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) :
    (∃ s : ((N.pull a).pull b).Gen, s.IsGen) ↔ ∃ s : (N.pull (b ≫ a)).Gen, s.IsGen := by
  have hb : ∀ z : Z, (b ≫ a).base z = a.base (b.base z) := fun z => rfl
  have m1 : ∀ (j : PUnit.{1} → N.ι) (z : Z), z ∈ (N.pull (b ≫ a)).U j →
      z ∈ ((N.pull a).pull b).U (fun _ _ => j PUnit.unit) := by
    intro j z hz
    have h1 : (b ≫ a).base z ∈ N.U (j PUnit.unit) := (mem_wchart_pu N (b ≫ a) j z).1 hz
    have h2 : b.base z ∈ (N.pull a).U (fun _ => j PUnit.unit) :=
      (mem_wchart_pu N a (fun _ => j PUnit.unit) (b.base z)).2 (by rw [← hb]; exact h1)
    exact (mem_wchart_pu (N.pull a) b (fun _ _ => j PUnit.unit) z).2 h2
  have m2 : ∀ (j : PUnit.{1} → PUnit.{1} → N.ι) (z : Z), z ∈ ((N.pull a).pull b).U j →
      z ∈ (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := by
    intro j z hz
    have h2 : b.base z ∈ (N.pull a).U (j PUnit.unit) := (mem_wchart_pu (N.pull a) b j z).1 hz
    have h1 : a.base (b.base z) ∈ N.U (j PUnit.unit PUnit.unit) :=
      (mem_wchart_pu N a (j PUnit.unit) (b.base z)).1 h2
    exact (mem_wchart_pu N (b ≫ a) (fun _ => j PUnit.unit PUnit.unit) z).2 (by rw [hb]; exact h1)
  constructor
  · intro h
    refine exists_gen_transfer (L := (N.pull a).pull b) (L' := N.pull (b ≫ a))
      (fun j _ _ => j PUnit.unit) m1 ?_ h
    intro i j y hy
    have hy' := pull_inf_le N (b ≫ a) i j hy
    exact (germ_pull N (b ≫ a) i j y hy hy').trans
      (germ_pull_pull N a b (fun _ _ => i PUnit.unit) (fun _ _ => j PUnit.unit) y ⟨m1 i y hy.1, m1 j y hy.2⟩ hy').symm
  · intro h
    refine exists_gen_transfer (L := N.pull (b ≫ a)) (L' := (N.pull a).pull b)
      (fun j _ => j PUnit.unit PUnit.unit) m2 ?_ h
    intro i j y hy
    have hy2 : y ∈ (N.pull (b ≫ a)).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := ⟨m2 i y hy.1, m2 j y hy.2⟩
    have hy' := pull_inf_le N (b ≫ a) _ _ hy2
    exact (germ_pull_pull N a b i j y hy hy').trans (germ_pull N (b ≫ a) _ _ y hy2 hy').symm

end GlobalTheory.TrivLocusLocal

namespace GlobalTheory.TrivLocusLocal

theorem exists_closed_triv_local : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S _ A _ L₀ N hA hL₀ ha hN hr x
  obtain ⟨R, j, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion j)
  letI : GrpObj ((Over.pullback j').obj A) := Functor.grpObjObj
  let φ₀ := pullback.fst A.hom j'
  have hp := isGrpPullback_pullback A j'
  have hB : IsAbelianScheme ((Over.pullback j').obj A) := Out.TLinPf.isAb_pullback j' A hA
  have hL₀' := pull_isLB hL₀ φ₀
  have haB : Out.RelAmple ((Over.pullback j').obj A) (L₀.pull φ₀) := by
    have := GlobalTheory.KTrivSpread.relAmple_chart j' (𝟙 _) hL₀ ha
    rwa [Category.id_comp] at this
  have hN' := pull_isLB hN φ₀
  have hrB : Out.Rigidified ((Over.pullback j').obj A) (N.pull φ₀) := by
    obtain ⟨s, hs⟩ := hr
    have h1 := exists_gen_pull_comp N (eSec A) j' ⟨s, hs⟩
    rw [← GlobalTheory.RigidBundleGlue.eSec_comm hp] at h1
    exact (exists_gen_pull_pull_iff N φ₀ (eSec ((Over.pullback j').obj A))).2 h1
  obtain ⟨Z, i₀, hi₀, H⟩ := GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified R ((Over.pullback j').obj A) (L₀.pull φ₀) (N.pull φ₀) hB hL₀' haB hN' hrB
  refine ⟨j'.opensRange, Z, i₀ ≫ j'.isoOpensRange.hom, hx, inferInstance, fun T t => ?_⟩
  let t' : T ⟶ Sp R := t ≫ j'.isoOpensRange.inv
  have ht : t' ≫ j' = t ≫ j'.opensRange.ι := by
    simp only [t', Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  letI : GrpObj ((Over.pullback t').obj ((Over.pullback j').obj A)) := Functor.grpObjObj
  have hq := isGrpPullback_pullback ((Over.pullback j').obj A) t'
  have H1 := H T t' _ _ hq
  have hP : IsPullback (pullback.fst ((Over.pullback j').obj A).hom t' ≫ φ₀)
      (pullback.snd ((Over.pullback j').obj A).hom t') A.hom (t ≫ j'.opensRange.ι) := by
    rw [← ht]
    exact (IsPullback.of_hasPullback ((Over.pullback j').obj A).hom t').paste_horiz
      (IsPullback.of_hasPullback A.hom j')
  rw [← trivCond_iff A N T (t ≫ j'.opensRange.ι) _ _ _ hP, ← exists_gen_pull_pull_iff]
  refine H1.trans ⟨fun ⟨z, hz⟩ => ⟨z, ?_⟩, fun ⟨z, hz⟩ => ⟨z, ?_⟩⟩
  · rw [← Category.assoc, hz]
    simp only [t', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [t', ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TrivLocusLocal
