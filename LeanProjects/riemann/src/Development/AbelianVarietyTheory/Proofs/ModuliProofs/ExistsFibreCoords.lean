import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_det_ne_zero_of_common_ker {K J : Type} [Field K] {g : ℕ} (φ : J → (Fin g → K) →ₗ[K] K)
    (h : ∀ w, (∀ i, φ i w = 0) → w = 0) :
    ∃ c : Fin g → J, (Matrix.of fun a b => φ (c b) (Pi.single a 1)).det ≠ 0 := by
  classical
  let ψ : J → Module.Dual K (Fin g → K) := φ
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hco : (Submodule.span K (Set.range ψ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      exact (Submodule.mem_bot K).2 (h w fun i => hw _ (Submodule.subset_span ⟨i, rfl⟩))
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span K (Set.range ψ))
    rw [hco, finrank_bot, add_zero] at hdim
    rw [hdim, Subspace.dual_finrank_eq]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range ψ)
  let B : Module.Basis b K (Module.Dual K (Fin g → K)) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let D : Module.Basis (Fin g) K (Module.Dual K (Fin g → K)) := (Pi.basisFun K (Fin g)).dualBasis
  let e : b ≃ Fin g := B.indexEquiv D
  have hex : ∀ k : Fin g, ∃ j, ψ j = ((e.symm k : b) : Module.Dual K (Fin g → K)) := fun k => hbsub (e.symm k).2
  choose c hc using hex
  refine ⟨c, ?_⟩
  have hM : (Matrix.of fun a k => φ (c k) (Pi.single a 1)) = D.toMatrix (B.reindex e) := by
    ext a k
    rw [Matrix.of_apply]
    change ψ (c k) (Pi.single a 1) = _
    rw [hc k]
    simp only [Module.Basis.toMatrix_apply, D, Module.Basis.dualBasis_repr,
      Module.Basis.reindex_apply, B, Module.Basis.mk_apply, Pi.basisFun_apply]
  rw [hM]
  intro h0
  have hone := congrArg Matrix.det (D.toMatrix_mul_toMatrix_flip (B.reindex e))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hone
  exact zero_ne_one hone

theorem top_le_preimage_finset_inf {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (s : Finset κ) (W : κ → X.Opens)
    (h : ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ W i) : ⊤ ≤ x ⁻¹ᵁ (s.inf W) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ p _
    simp
  | @insert a s ha ih =>
    intro h p hp
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a s) hp, ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hp⟩

theorem fderiv_fn_resG {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    {X : Scheme.{0}} (m : A₀.left ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  have key : ∀ (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ W' → valAt' y W' (resG X h f) = valAt' y W f := by
    intro y hy
    have hy2 : ⊤ ≤ y ⁻¹ᵁ W := hy.trans (fun q hq => h hq)
    unfold valAt'
    rw [dif_pos hy, dif_pos hy2]
    unfold valAt
    congr 1
    rw [← Scheme.Hom.map_appLE y hy (homOfLE h).op]
    rfl
  have hopen : IsOpen (dom u m W') := by
    exact (u.hol (m ⁻¹ᵁ W') 0).1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  exact key _ hz'

theorem exists_fibre_coords : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb z
  let J : Type := {Wf : (W : X.Opens) × Γ(X, W) // z ∈ dom u m Wf.1}
  let φ : J → (Fin P₀.g → ℂ) →ₗ[ℂ] ℂ := fun j => (fderiv ℂ (fn u m j.1.1 j.1.2) z).toLinearMap
  have hker : ∀ w, (∀ j, φ j w = 0) → w = 0 := by
    intro w hw
    have hδ : PtDer ((u.ex z).left ≫ m) (fun _ _ => (0 : ℂ)) :=
      ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
    obtain ⟨w₀, _, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z (fun _ _ => 0) hδ (fun _ => rfl)
    have e1 : w = w₀ := huniq w (fun W f hzW => (hw ⟨⟨W, f⟩, hzW⟩).symm)
    have e2 : (0 : Fin P₀.g → ℂ) = w₀ := huniq 0 (fun W f _ => (ContinuousLinearMap.map_zero _).symm)
    exact e1.trans e2.symm
  obtain ⟨c, hc⟩ := exists_det_ne_zero_of_common_ker φ hker
  have hzW : z ∈ dom u m (Finset.univ.inf fun b => (c b).1.1) :=
    top_le_preimage_finset_inf ((u.ex z).left ≫ m) Finset.univ (fun b => (c b).1.1) (fun b _ => (c b).2)
  refine ⟨Finset.univ.inf fun b => (c b).1.1,
    fun b => resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2, hzW, ?_⟩
  have hE : (Matrix.of fun a b => fderiv ℂ (fn u m (Finset.univ.inf fun b => (c b).1.1)
      (resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2)) z (Pi.single a 1)) =
      Matrix.of fun a b => φ (c b) (Pi.single a 1) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [fderiv_fn_resG u m (Finset.inf_le (Finset.mem_univ b)) (c b).1.2 hzW]
    rfl
  rw [hE]
  exact hc

end GlobalTheory.KS
