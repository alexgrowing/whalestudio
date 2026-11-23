import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockInnerProductPosDefCompactMatrixUnitAdjointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetMatrixUnitCompactTotalDegreeLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryRepresentativesExistVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightKTypeMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LowestKType

theorem lowestKType_irreducible : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ S : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ S, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ S, ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0) → (∀ ψ ∈ S, ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ)) ∘ₗ ψ ∈ S) → S ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ S := by
  intro D n m w BS K _ r hU1 hU2 W _ _ _ ρ hρ S hSeq hSharm hSstab hS0 φ hφeq hφharm
  classical
  have hinj : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) →
      ψ ≠ 0 → Function.Injective ψ := by
    intro ψ hψ h0
    rw [← LinearMap.ker_eq_bot]
    rcases hρ (LinearMap.ker ψ) (fun k => Submodule.map_le_iff_le_comap.2 fun x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
      rw [hψ, hx, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ext fun x => by
        have : x ∈ LinearMap.ker ψ := h ▸ Submodule.mem_top
        simpa using this) h0
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hseq := hSeq s hsS
  have hsinj := hinj s hseq hs0
  choose A hA using fun τ a b => GlobalTheory.T.unitary_representatives_exist_vector D n m w BS K r hU2 W ρ s hsinj hseq τ a b
  have hV0 : LinearMap.range s ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  have hVst : ∀ P ∈ LinearMap.range s, ∀ (τ : D.what₂.Tau) (a b : Fin n),
      GlobalTheory.LowestKType.sop w τ a b P ∈ LinearMap.range s := by
    rintro _ ⟨x, rfl⟩ τ a b
    exact ⟨A τ a b x, by simpa using LinearMap.congr_fun (hA τ a b s hseq) x⟩
  obtain ⟨P0, ⟨w0, rfl⟩, hP0, lam, hlam⟩ := GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace D n m w _ inferInstance hV0 hVst
  have hw0 : w0 ≠ 0 := by rintro rfl; exact hP0 (map_zero s)
  have hN : ∀ φ' : W →ₗ[ℂ] PolF D m n,
      (∀ (k : K) (x : W), φ' (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ' x)) →
      GlobalTheory.LowestKType.IsNHw w lam (φ' w0) := by
    intro φ' hφ'
    refine ⟨fun τ a b hab => ?_, fun τ a => ?_⟩
    · have h1 : s (A τ a b w0) = 0 := by
        rw [show s (A τ a b w0) = GlobalTheory.LowestKType.sop w τ a b (s w0) from LinearMap.congr_fun (hA τ a b s hseq) w0]
        exact hlam.1 τ a b hab
      have h2 : A τ a b w0 = 0 := hsinj (by rw [h1, map_zero])
      have h3 := LinearMap.congr_fun (hA τ a b φ' hφ') w0
      simp only [LinearMap.comp_apply, h2, map_zero] at h3
      exact h3.symm
    · have h1 : s (A τ a a w0) = s (lam τ a • w0) := by
        rw [show s (A τ a a w0) = GlobalTheory.LowestKType.sop w τ a a (s w0) from LinearMap.congr_fun (hA τ a a s hseq) w0,
          map_smul]
        exact hlam.2 τ a
      have h3 := LinearMap.congr_fun (hA τ a a φ' hφ') w0
      simp only [LinearMap.comp_apply, hsinj h1, map_smul] at h3
      exact h3.symm
  let J := {j : D.what₂.Tau × Fin m × Fin m // GlobalTheory.LowestKType.Cpt w j.1 j.2.1 j.2.2}
  let E : J → Module.End ℂ (W →ₗ[ℂ] PolF D m n) := fun j =>
    LinearMap.llcomp ℂ W (PolF D m n) (PolF D m n) (GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2)
  have hE : ∀ j ψ, E j ψ = GlobalTheory.LowestKType.kop w j.1.1 j.1.2.1 j.1.2.2 ∘ₗ ψ := fun _ _ => rfl
  let st : J → J := fun j => ⟨(j.1.1, j.1.2.2, j.1.2.1), Iff.symm j.2⟩
  obtain ⟨B, hBpos, hBani, hBadj⟩ := GlobalTheory.T.fockInnerProduct_posDef_compact_matrixUnit_adjoint D n m
  let e := Module.finBasis ℂ W
  let BM : (W →ₗ[ℂ] PolF D m n) →ₗ⋆[ℂ] (W →ₗ[ℂ] PolF D m n) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ψ χ => ∑ i, B (ψ (e i)) (χ (e i)))
      (fun ψ ψ' χ => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
      (fun ψ χ χ' => by simp [Finset.sum_add_distrib])
      (fun c ψ χ => by simp [Finset.mul_sum])
  have hBM : ∀ ψ χ, BM ψ χ = ∑ i, B (ψ (e i)) (χ (e i)) := fun _ _ => rfl
  have hBMani : ∀ ψ : W →ₗ[ℂ] PolF D m n, BM ψ ψ = 0 → ψ = 0 := by
    intro ψ h
    rw [hBM] at h
    have hre : ∑ i, (B (ψ (e i)) (ψ (e i))).re = 0 := by
      have := congrArg Complex.re h
      simpa [Complex.re_sum] using this
    have hz : ∀ i, B (ψ (e i)) (ψ (e i)) = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hBpos (ψ (e i))).2)).1 hre i (Finset.mem_univ _)
      exact Complex.ext this (hBpos _).1
    exact e.ext fun i => by rw [hBani _ (hz i), LinearMap.zero_apply]
  have hBMadj : ∀ j ψ χ, BM (E j ψ) χ = BM ψ (E (st j) χ) := by
    intro j ψ χ
    simp only [hBM, hE, LinearMap.comp_apply]
    exact Finset.sum_congr rfl fun i _ => hBadj w _ _ _ j.2 _ _
  obtain ⟨d, hdφ, hds⟩ : ∃ d, (∀ i, (φ (e i)).totalDegree ≤ d) ∧ ∀ i, (s (e i)).totalDegree ≤ d :=
    ⟨Finset.univ.sup (fun i => (φ (e i)).totalDegree) ⊔ Finset.univ.sup (fun i => (s (e i)).totalDegree),
      fun i => le_sup_of_le_left (Finset.le_sup (f := fun i => (φ (e i)).totalDegree) (Finset.mem_univ i)),
      fun i => le_sup_of_le_right (Finset.le_sup (f := fun i => (s (e i)).totalDegree) (Finset.mem_univ i))⟩
  have hdeg : ∀ ψ : W →ₗ[ℂ] PolF D m n, (∀ i, (ψ (e i)).totalDegree ≤ d) →
      ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d := by
    intro ψ hψ x
    rw [← e.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hψ i))
  let U : Submodule ℂ (W →ₗ[ℂ] PolF D m n) :=
    { carrier := {ψ | (∀ (k : K) (x : W), ψ (ρ k x) = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ x)) ∧
        (∀ x, GlobalTheory.LowestKType.IsHarm w (ψ x)) ∧ ∀ x, ψ x ∈ MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d}
      add_mem' := by
        rintro ψ χ ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
        refine ⟨fun k x => by simp [h1, g1], fun x τ i l hi hl => ?_, fun x => add_mem (h3 x) (g3 x)⟩
        simp only [LinearMap.add_apply, map_add, h2 x τ i l hi hl, g2 x τ i l hi hl, add_zero]
      zero_mem' := ⟨fun k x => by simp, fun x τ i l _ _ => by simp, fun x => zero_mem _⟩
      smul_mem' := by
        rintro c ψ ⟨h1, h2, h3⟩
        refine ⟨fun k x => by simp [h1], fun x τ i l hi hl => ?_, fun x => Submodule.smul_mem _ c (h3 x)⟩
        simp only [LinearMap.smul_apply, map_smul, h2 x τ i l hi hl, smul_zero] }
  have hUfd : FiniteDimensional ℂ U := by
    let f : U →ₗ[ℂ] (Fin (Module.finrank ℂ W) → MvPolynomial.restrictTotalDegree (FVar D m n) ℂ d) :=
      { toFun := fun ψ i => ⟨(ψ : W →ₗ[ℂ] PolF D m n) (e i), ψ.2.2.2 (e i)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    exact Module.Finite.of_injective f (fun ψ χ h => Subtype.ext (e.ext fun i => by
      have := congrArg (fun g => (g i : PolF D m n)) h
      simpa [f] using this))
  have hUst : ∀ j, ∀ ψ ∈ U, E j ψ ∈ U := by
    rintro ⟨⟨τ, a, b⟩, hab⟩ ψ ⟨h1, h2, h3⟩
    refine ⟨fun k x => ?_, fun x => ?_, fun x => ?_⟩
    · show GlobalTheory.LowestKType.kop w τ a b (ψ (ρ k x)) =
        GlobalTheory.ExportSeries.fockGL m w BS (r k) (GlobalTheory.LowestKType.kop w τ a b (ψ x))
      rw [h1, GlobalTheory.ExportSeries.fockGL_apply, GlobalTheory.ExportSeries.fockGL_apply, map_smul]
      congr 1
      exact (GlobalTheory.FockSubstComm.fockSubst_fockT D m n w.p _ τ _ _).symm
    · exact GlobalTheory.CompactHarm.fockT_compact_harm D n m w.p (ψ x) (h2 x) τ a b hab
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.T.fockTargetMatrixUnit_compact_totalDegree_le D n m w τ a b hab d _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 (h3 x)))
  have hsU : s ∈ U := ⟨hseq, hSharm s hsS, hdeg s hds⟩
  have hφU : φ ∈ U := ⟨hφeq, hφharm, hdeg φ hdφ⟩
  have hKHw : ∀ x : W →ₗ[ℂ] PolF D m n, GlobalTheory.LowestKType.IsKHwMap w x → GlobalTheory.LowestKType.IsKHw w (x w0) :=
    fun x hxh => ⟨fun τ a b hab hlt => by simpa using LinearMap.congr_fun (hxh.1 τ a b hab hlt) w0,
      fun τ a => (hxh.2 τ a).imp fun c hc => by simpa using LinearMap.congr_fun hc w0⟩
  have key := GlobalTheory.T.isIrreducible_of_anisotropic_form_highestWeight (W →ₗ[ℂ] PolF D m n) U hUfd J E st BM (GlobalTheory.LowestKType.IsKHwMap w) hUst
    (fun x _ => hBMani x) hBMadj (fun j => rfl)
    (fun T hTU hT0 hTst => by
      haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTU
      exact GlobalTheory.T.exists_highest_weight_K_type_map D n m w W T inferInstance hT0 (fun ψ hψ τ a b hab => hTst ⟨(τ, a, b), hab⟩ ψ hψ))
    (fun x y hx hy hxh hyh hx0 => by
      obtain ⟨c, hc⟩ := GlobalTheory.T.jointHarmonic_highestWeight_multiplicity_one D n m w lam (x w0) (y w0)
        (fun h => hw0 (hinj x hx.1 hx0 (h.trans (map_zero x).symm))) (hx.2.1 w0) (hy.2.1 w0)
        (hN x hx.1) (hN y hy.1) (hKHw x hxh) (hKHw y hyh)
      refine ⟨c, ?_⟩
      by_contra hne
      have h0 : y - c • x ≠ 0 := sub_ne_zero.2 hne
      have := hinj (y - c • x) (fun k z => by simp [hx.1, hy.1]) h0
        (show (y - c • x) w0 = (y - c • x) 0 by simp [hc])
      exact hw0 this)
  have hS'U : S ⊓ U = U := key (S ⊓ U) inf_le_right (by
      intro h
      apply hs0
      have : s ∈ S ⊓ U := ⟨hsS, hsU⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this)
    (fun j ψ hψ => ⟨hSstab ψ hψ.1 j.1.1 j.1.2.1 j.1.2.2 j.2, hUst j ψ hψ.2⟩)
  have : φ ∈ S ⊓ U := by rw [hS'U]; exact hφU
  exact this.1

end GlobalTheory.LowestKType
