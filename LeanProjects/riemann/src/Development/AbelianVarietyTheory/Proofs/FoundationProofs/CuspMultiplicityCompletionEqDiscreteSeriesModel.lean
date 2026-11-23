import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyEqOfMemHomFinDS
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutMult

open scoped InnerProductSpace
open GlobalTheory.Cusp

open Classical in

theorem rank_homIn_eq_rank_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} (hirr : σ.IsIrreducible)
    (hadm : IsAdmissible σ) (hcopy : IsCopyFinDS σ M π ⊤) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : GA D V →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) {U : Submodule ℂ K} (hU : IsClosed (U : Set K)) :
    Module.rank ℂ (homIn π ρ U) = Module.rank ℂ (homFinDS σ M ρ U) := by
  obtain ⟨T, hT, hinj, hd⟩ := hcopy
  have hTm := mem_homTensorPi.1 hT
  let f : homIn π ρ U →ₗ[ℂ] (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) :=
    { toFun := fun A => (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H K (A : H →L[ℂ] K)).toLinearMap ∘ₗ T
      map_add' := fun A B => by ext w y; simp
      map_smul' := fun c A => by ext w y; simp }
  have hmem : ∀ A, f A ∈ homFinDS σ M ρ U := fun A => by
    refine mem_homTensorPi.2 ⟨fun w y => ?_, fun g w y => ?_, fun i g w y => ?_⟩
    · exact A.2.1 _
    · change (A : H →L[ℂ] K) (T (σ g w) y) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.1 g w y)).trans (A.2.2 _ _)
    · change (A : H →L[ℂ] K) (T w _) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.2 i g w y)).trans (A.2.2 _ _)
  let F : homIn π ρ U →ₗ[ℂ] homFinDS σ M ρ U := f.codRestrict _ hmem
  have hdense : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  have hbij : Function.Bijective F := by
    constructor
    · intro A B hAB
      have e : ∀ w y, (A : H →L[ℂ] K) (T w y) = (B : H →L[ℂ] K) (T w y) := fun w y =>
        congrArg (fun Φ : homFinDS σ M ρ U => ((Φ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) w) y) hAB
      refine Subtype.ext (ContinuousLinearMap.ext_on hdense ?_)
      rintro _ ⟨w, y, rfl⟩
      exact e w y
    · intro Φ
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hirr hadm H π hπ T hT hinj hd K ρ hρ U hU Φ.1 Φ.2
      exact ⟨⟨A, hA⟩, Subtype.ext (LinearMap.ext fun w => ContinuousMultilinearMap.ext fun y => hAe w y)⟩
  exact (LinearEquiv.ofBijective F hbij).rank_eq

open Classical in

theorem mCusp_eq_mCuspDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  intro D V S M μ _ _ H _ _ π hπ W _ _ σ hirr hadm hcopy
  haveI : CompleteSpace H := hπ.complete
  exact rank_homIn_eq_rank_homFinDS hπ.unitary hirr hadm hcopy (isUnitaryRep_RG V μ) (isSubrep_L2cusp V μ).1

end GlobalTheory.AutMult
