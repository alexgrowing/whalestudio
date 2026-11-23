import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijOnKerAndExactOfQuasiIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMatricesOfProjectiveComplex
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactCechOneOfH1Zero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw.PerfOfModel

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {Y Y' : Scheme.{0}}
  {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')} {π : Y' ⟶ Y}
  (M : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def termMap (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ) :
    R' ⊗[R] (cechLB f M D).X p →ₗ[R'] (cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).X p :=
  secTermBaseChange M D w (p + 1)

theorem d_termMap (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ)
    (x : R' ⊗[R] (cechLB f M D).X p) :
    ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d p (p + 1)).hom (termMap M D w p x) =
      termMap M D w (p + 1) (((cechLB f M D).d p (p + 1)).hom.baseChange R' x) := by
  rw [cechLB_d, cechLB_d]
  exact d_secTermBaseChange M D w (p + 1) x

variable {M D}

theorem termMap_bijective [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (p : ℕ) :
    Function.Bijective (termMap M D H.w p) :=
  secTermBaseChange_bijective hM H (p + 1) fun s hs => hD s (Finset.card_pos.1 (by omega))

theorem termMap_bijOn [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    Set.BijOn (termMap M D H.w 0) (LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R'))
      (LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom) := by
  have key (x : R' ⊗[R] (cechLB f M D).X 0) :
      termMap M D H.w 0 x ∈ LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom ↔
        x ∈ LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R') := by
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact (d_termMap M D H.w 0 x).congr_left.trans
      (map_eq_zero_iff _ (termMap_bijective hM H hD 1).1)
  refine ⟨fun x hx => (key x).2 hx, (termMap_bijective hM H hD 0).1.injOn, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := (termMap_bijective hM H hD 0).2 y
  exact ⟨x, (key x).1 hy, rfl⟩

theorem exact_baseChange [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (h : Function.Exact ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom
      ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 1 2).hom) :
    Function.Exact (((cechLB f M D).d 0 1).hom.baseChange R')
      (((cechLB f M D).d 1 2).hom.baseChange R') := by
  intro x
  have e₁ := d_termMap M D H.w 1 x
  refine (map_eq_zero_iff _ (termMap_bijective hM H hD 2).1).symm.trans
    (e₁.congr_left.symm.trans ((h _).trans ⟨?_, ?_⟩))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (termMap_bijective hM H hD 0).2 y
    exact ⟨z, (termMap_bijective hM H hD 1).1 ((d_termMap M D H.w 0 z).symm.trans hy)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, d_termMap M D H.w 0 z⟩

theorem iSup_preimage (π : Y' ⟶ Y) (hc : ⨆ i, D i = ⊤) : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

theorem coord_termMap_sum (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    {a : ℕ} (v : Fin a → R') (x : Fin a → (cechLB f M D).X 0)
    (s : {s : Finset κ // s.card = 0 + 1}) (j : M.ι)
    (h : π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j) ≤ (⨅ i ∈ s.1, π ⁻¹ᵁ D i) ⊓ (M.pull π).U fun _ => j) :
    rs Y' h (SecOnR.coord (f := f') (termMap M D w 0 (∑ k, v k ⊗ₜ[R] x k) s) fun _ => j) =
      ∑ k, cst f' (π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j)) (v k) *
        (π.app _).hom (SecOnR.coord (f := f) (x k s) j) := by
  let F : (cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).X 0 →+
      Γ(Y', π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j)) :=
    AddMonoidHom.mk' (fun y => rs Y' h (SecOnR.coord (f := f') (y s) fun _ => j))
      fun y z => map_add (rs Y' h) _ _
  change F (termMap M D w 0 _) = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change rs Y' h (SecOnR.coord (f := f') (v k • SecOnR.pull M w _ _ (preimage_biInf D π s.1).ge (x k s)) fun _ => j) = _
  refine (congrArg (rs Y' h) (SecOnR.coord_base_smul _ _ _)).trans
    ((map_mul (rs Y' h) _ _).trans (congrArg₂ (· * ·) (rs_cst f' h _) ?_))
  refine (congrArg (rs Y' h) (SecOn.coord_pullLE π (preimage_biInf D π s.1).ge (x k s) _)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  exact GlobalTheory.LB.resG_appLE π _ _ _

end GlobalTheory.AbLaw.PerfOfModel

namespace GlobalTheory.AbLaw

open PerfOfModel

theorem perf_of_projective_model :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M D), M.IsLB → ⨆ i, D i = ⊤ → (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ((∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) → Nonempty (Perf f M) := by
  intro R _ Y f M κ _ _ D K φ hM hc hD ⟨hK, hq⟩
  haveI := fun p => (hK p).1
  haveI := fun p => (hK p).2
  obtain ⟨a, b, c, D₀, D₁, u, hcomp, hmat⟩ := exists_matrices_of_projective_complex R (K.X 0)
    (K.X 1) (K.X 2) (K.d 0 1).hom (K.d 1 2).hom
    (LinearMap.ext fun x => cochain_d_d_apply K 0 1 2 x)
  refine ⟨{
    a := a, b := b, c := c, D₀ := D₀, D₁ := D₁, comp := hcomp
    I := κ × M.ι
    W := fun p => (⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2
    ch := fun p => p.2
    le := fun _ => inf_le_right
    cover := ?_
    u := fun k p => SecOnR.coord (f := f) ((φ.f 0).hom (u k) ⟨{p.1}, Finset.card_singleton _⟩) p.2
    sec := ?_
    exact := ?_ }⟩
  · simp only [Finset.iInf_singleton]
    rw [iSup_prod]
    refine top_unique fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hi, hj⟩⟩
  · intro R' _ g Y' π f' H
    letI := g.toAlgebra
    have B := ((termMap_bijOn hM H hD).comp
      (bijOn_ker_and_exact_of_quasiIso_baseChange R R' K _ φ (hq R')).1).comp (hmat R').1
    let S := CechOne.secKerEquiv (M.pull π) f' (iSup_preimage π hc)
    refine ⟨(B.equiv _).trans S.symm.toEquiv, fun v p => ?_⟩
    have hv : (S (S.symm (B.equiv _ v))).1 =
        termMap M D H.w 0 (∑ k, v.1 k ⊗ₜ[R] (φ.f 0).hom (u k)) := by
      rw [S.apply_symm_apply]
      change termMap M D H.w 0 ((φ.f 0).hom.baseChange R' (∑ k, v.1 k ⊗ₜ[R] u k)) = _
      rw [map_sum ((φ.f 0).hom.baseChange R')]
      rfl
    have hle : π ⁻¹ᵁ ((⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2) ≤
        (⨅ i ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D i) ⊓ (M.pull π).U fun _ => p.2 :=
      le_inf ((π.preimage_mono inf_le_left).trans (preimage_biInf D π _).le)
        (le_pull M π inf_le_right)
    refine Eq.trans ?_ (coord_termMap_sum H.w v.1 (fun k => (φ.f 0).hom (u k))
      ⟨{p.1}, Finset.card_singleton _⟩ p.2 hle)
    rw [← hv, CechOne.secKerEquiv_val]
    exact (rs_rs inf_le_right hle _).symm
  · intro R' _ g Y' π f' H h1
    letI := g.toAlgebra
    refine (hmat R').2 ((bijOn_ker_and_exact_of_quasiIso_baseChange R R' K _ φ (hq R')).2
      (exact_baseChange hM H hD ?_))
    rw [cechLB_d f' _ _ 0, cechLB_d f' _ _ 1]
    exact GlobalTheory.Cohom.exact_cech_one_of_h1Zero R' Y' f' _ κ _ (LB.isLB_pull hM π)
      (iSup_preimage π hc) h1

end GlobalTheory.AbLaw
