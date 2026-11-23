import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SegreGlue
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem sec_sub (k : Type) [Field k] (d : ℕ) (a : MvPolynomial (Fin (d + 2)) k) :
    a - rename Fin.succ (killCompl (R := k) (Fin.succ_injective (d + 1)) a) ∈
      Ideal.span {(X 0 : MvPolynomial (Fin (d + 2)) k)} := by
  induction a using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    rw [map_mul, map_mul]
    cases n using Fin.cases with
    | zero =>
      have h0 : killCompl (R := k) (Fin.succ_injective (d + 1)) (X 0) = 0 := by
        simp [killCompl, aeval_X, Fin.succ_ne_zero]
      rw [h0, map_zero, mul_zero, sub_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | succ j =>
      have h1 : rename Fin.succ (killCompl (R := k) (Fin.succ_injective (d + 1)) (X j.succ)) =
          X j.succ := by
        simp [killCompl, aeval_X]
      rw [h1, ← sub_mul]
      exact Ideal.mul_mem_right _ _ hp

attribute [local instance] MvPolynomial.gradedAlgebra in
private def chartIso (k : Type) [Field k] (d : ℕ) :
    (GlobalTheory.ProjSpace.chart k (d + 1) 0 : Scheme.{0}) ≅ Spec (CommRingCat.of (MvPolynomial (Fin (d + 1)) k)) :=
  Proj.basicOpenIsoSpec _ (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X k 0 |> (MvPolynomial.mem_homogeneousSubmodule _ _).2) one_pos ≪≫
    Scheme.Spec.mapIso (((GroundTheory.Arith.SchemeCoh.ProjSpace.chartEquiv k (0 : Fin (d + 2))).trans
      (MvPolynomial.renameEquiv k (finSuccAboveEquiv (0 : Fin (d + 2))).symm).toRingEquiv).toCommRingCatIso).symm.op

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem off_hyp (k : Type) [Field k] (d : ℕ) :
    Off (GlobalTheory.ProjSpace.linearι k (Fin.succ_injective (d + 1))) (GlobalTheory.ProjSpace.chart k (d + 1) 0) := by
  unfold Off
  ext x
  constructor
  · rintro hx ⟨y, rfl⟩
    have hb := GlobalTheory.ProjSpace.linearι_preimage_chart_of_notMem k (Fin.succ_injective (d + 1))
      (k := 0) (by simp [Fin.succ_ne_zero])
    have hy : y ∈ GlobalTheory.ProjSpace.linearι k (Fin.succ_injective (d + 1)) ⁻¹ᵁ
        GlobalTheory.ProjSpace.chart k (d + 1) 0 := hx
    rw [hb] at hy
    exact hy
  · intro hx
    by_contra hc
    have h0 : (X 0 : MvPolynomial (Fin (d + 2)) k) ∈ x.asHomogeneousIdeal := by
      by_contra h
      exact hc h
    let ρ : GlobalTheory.ProjSpace.grading k d →+*ᵍ GlobalTheory.ProjSpace.grading k (d + 1) :=
      { toRingHom := (rename (R := k) Fin.succ).toRingHom
        map_mem := fun {i a} ha => by
          have ha' := (mem_homogeneousSubmodule _ _).1 ha
          exact (mem_homogeneousSubmodule _ _).2 (ha'.rename_isHomogeneous) }
    have hρ : ∀ a, ρ a = rename Fin.succ a := fun a => rfl
    have hrel : ¬ HomogeneousIdeal.irrelevant (GlobalTheory.ProjSpace.grading k d) ≤
        x.asHomogeneousIdeal.comap ρ := by
      intro hle
      have htop := GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X (A := k) (n := d + 1)
      have hxm : x ∈ (⊤ : (Proj (GlobalTheory.ProjSpace.grading k (d + 1))).Opens) := trivial
      rw [← htop, TopologicalSpace.Opens.mem_iSup] at hxm
      obtain ⟨j, hj⟩ := hxm
      cases j using Fin.cases with
      | zero => exact hj h0
      | succ i =>
        have hi := hle (GroundTheory.Arith.SchemeCoh.ProjSpace.X_mem_irrelevant (A := k) (n := d) i)
        change ρ (X i) ∈ x.asHomogeneousIdeal at hi
        rw [hρ, rename_X] at hi
        exact hj hi
    let y : ProjectiveSpectrum (GlobalTheory.ProjSpace.grading k d) :=
      ⟨x.asHomogeneousIdeal.comap ρ, x.2.comap ρ, hrel⟩
    apply hx
    refine ⟨y, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.toIdeal_injective
    ext a
    change rename Fin.succ (killCompl (R := k) (Fin.succ_injective (d + 1)) a) ∈
      x.asHomogeneousIdeal ↔ a ∈ x.asHomogeneousIdeal
    have hs := sec_sub k d a
    have hs' : a - rename Fin.succ (killCompl (R := k) (Fin.succ_injective (d + 1)) a) ∈
        x.asHomogeneousIdeal.toIdeal :=
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 h0)) hs
    constructor
    · intro h
      have h2 := Ideal.add_mem _ hs' h
      rwa [sub_add_cancel] at h2
    · intro h
      have h2 := Ideal.sub_mem _ h hs'
      rwa [sub_sub_cancel] at h2

theorem UpperTheory.Gal.KunnethLefschetz.hypEmb_holds :
    UpperTheory.Gal.KunnethLefschetz.HypEmb := by
  intro k _ d
  refine ⟨GlobalTheory.ProjSpace.linearι k (Fin.succ_injective (d + 1)), GlobalTheory.ProjSpace.chart k (d + 1) 0, inferInstance,
    GlobalTheory.ProjSpace.linearι_str k _, off_hyp k d, ⟨chartIso k d⟩⟩
