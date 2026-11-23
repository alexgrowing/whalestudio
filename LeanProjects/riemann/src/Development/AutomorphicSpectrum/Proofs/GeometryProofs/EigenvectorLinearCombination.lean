import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CombEig

theorem pt_sum {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∀ {n : ℕ} (e : Fin n → V), M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod
  | 0, e => by simpa using M.pt_zero
  | n + 1, e => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, pt_sum M]

theorem isEigVec_comb : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  intro S G _ _ F _ x P _ act σ n v cf w hv hc
  have key : ∀ y : epsAt x ⟶ G, IsEigVec act x σ y ↔
      (IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y) := by
    intro y
    unfold IsEigVec
    refine and_congr_right fun _ => forall_congr' fun a => ?_
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [h]
      rfl
    · intro h
      rw [h]
      rfl
  have hcomm : ∀ c d : F, LieTangent.epsScale x c ≫ LieTangent.epsScale x d =
      LieTangent.epsScale x d ≫ LieTangent.epsScale x c := by
    intro c d
    have hr : (epsMul c).comp (epsMul d) = (epsMul d).comp (epsMul c) := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
      · simp [LieTangent.epsMul_fst]
      · simp [LieTangent.epsMul_snd, mul_left_comm]
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (epsMul c)) ≫ Spec.map (CommRingCat.ofHom (epsMul d)) =
      Spec.map (CommRingCat.ofHom (epsMul d)) ≫ Spec.map (CommRingCat.ofHom (epsMul c))
    rw [LieTangent.spec_comp, LieTangent.spec_comp, hr]
  obtain ⟨u, hu, rfl⟩ := hc
  have hu' : ∀ i, u i = LieTangent.epsScale x (cf i) ≫ v i := by
    intro i
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  rw [key]
  apply List.prod_induction
    (fun y => IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y)
  · rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨LieTangent.isTanAt_mul hy hz, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
  · refine ⟨LieTangent.isTanAt_one, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.one_comp, MonObj.comp_one]
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [hu']
    obtain ⟨ht, he⟩ := (key (v i)).mp (hv i)
    refine ⟨LieTangent.isTanAt_scale (cf i) ht, fun a => ?_⟩
    rw [Category.assoc, he a, ← Category.assoc, ← Category.assoc, hcomm]

end GlobalTheory.CompanionTheory.Ar.CombEig
