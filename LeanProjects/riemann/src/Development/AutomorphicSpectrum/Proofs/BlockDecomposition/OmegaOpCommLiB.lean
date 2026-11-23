import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Sm E a →ₗ[ℂ] AutomorphicForm.archSmooth E a where
  toFun φ := ⟨φ.1, sm_mem_archSmooth E a φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smL_injective : Function.Injective (smL E a) := fun _ _ h =>
  Subtype.ext (congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1) h)

def liB (X : (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  lie E a (mMap E a (X : ArchMatrix E a))

def lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  ∑ i, liB (b i) * liB (b i)

def omegaOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ) :
    Module.End ℂ (Sm E a) :=
  ∑ i, (ε i : ℂ) • (liB (b i) * liB (b i))

theorem smL_liB (X : (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (liB X ψ) = uAction (UniversalEnvelopingAlgebra.ι ℝ X) (smL E a ψ) := by
  apply Subtype.ext
  funext g
  rw [uAction_ι_apply]
  change lieD (mMap E a (X : ArchMatrix E a)) ψ.1 g = _
  have h1 := (isExpLieAlgebra E a).hasDerivAt_rightDeriv (sm_mem_archSmooth E a ψ g)
    ((isExpLieAlgebra E a).ofLie X) 1
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  have hc : HasDerivAt (fun t : ℝ => toL (toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))).val) (mMap E a (X : ArchMatrix E a)) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (X : ArchMatrix E a)))
        (NormedSpace.exp ((0 : ℝ) • (X : ArchMatrix E a)) * (X : ArchMatrix E a)) 0 :=
      hasDerivAt_exp_smul_const (X : ArchMatrix E a) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    have h4 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact toL_toGL E a _
  have h0 : toGL E a ((isExpLieAlgebra E a).expG ((0 : ℝ) • (isExpLieAlgebra E a).ofLie X)) = 1 := by
    simp [toGL]
  have h2 := hasDerivAt_curve ψ g (fun t => toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))) (mMap E a (X : ArchMatrix E a)) h0 hc
  refine h2.unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  simp only [archSlice_apply, one_mul, infEmb_eq]

theorem smL_lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (lapOp b ψ) = ∑ i, uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
      (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) (smL E a ψ)) := by
  simp only [lapOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply, smL_liB]

theorem smL_omegaOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (ψ : Sm E a) : smL E a (omegaOp b ε ψ) = uAction (casimir b ε) (smL E a ψ) := by
  simp only [omegaOp, casimir, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    Module.End.mul_apply, smL_liB, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext g
  simp [Complex.real_smul]

theorem omegaOp_comm_liB {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (X : (isExpLieAlgebra E a).lieSubalgebra) :
    omegaOp b ε * liB X = liB X * omegaOp b ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hz : casimir b ε ∈ (isExpLieAlgebra E a).centerU :=
    casimir_mem_center hε2 horth archTraceForm_symm archTraceForm_lie
  have hc := Subalgebra.mem_center_iff.1 hz (UniversalEnvelopingAlgebra.ι ℝ X)
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, smL_liB, smL_liB, smL_omegaOp,
    ← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]

end GlobalTheory.CompanionTheory.HCRep

end
