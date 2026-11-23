import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem exp_mem (hX : X ∈ lieAt V τ) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t

theorem isAtTau_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (t : ℝ) :
    IsAtTau θ V τ (NormedSpace.exp (t • X)) (oneP θ V τ X t) :=
  GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (exp_mem hX t)

theorem oneP_add (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (exp_mem hX s) (exp_mem hX t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

theorem oneP_zero (hθ : IsInfFam θ) : oneP θ V τ X 0 = 1 := by
  unfold oneP
  rw [zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ]

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) i j)
      ((NormedSpace.exp (t • X) * X : Matrix (Fin n) (Fin n) ℂ) i j) t := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt t h

end

theorem continuous_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) : Continuous (oneP θ V τ X) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
    (continuous_matrix fun i j => continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_entry X t i j).continuousAt)
    (exp_mem hX)

theorem hasDerivAt_oneP (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {φ φ' : GA D V → ℂ}
    (h : ∀ g, HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (φ' g) 0) (g : GA D V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * oneP θ V τ X s)) (φ' (g * oneP θ V τ X t)) t := by
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h (g * oneP θ V τ X t))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← oneP_add hθ hX, add_sub_cancel]

theorem hasDerivAt_Rder {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hX : X ∈ lieAt V τ) (g : GA D V) :
    HasDerivAt (fun t : ℝ => φ (g * oneP θ V τ X t)) (Rder θ V τ X φ g) 0 :=
  (differentiable_oneP hφ hX g 0).hasDerivAt

attribute [local instance 100] LieRing.ofAssociativeRing in

theorem glRel_derEnd (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : Formalism.REAL.GlRel fun a b : Fin V.rank =>
    GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨P, Q, hPQ, h⟩ := GlobalTheory.T.unitary_lie_generators_rep _ _ (R.1 τ).1 (R.1 τ).2
  have hG := (h _ (fun X => GlobalTheory.SmoothForms.opInf R (atPlace V τ X)) (GlobalTheory.SmoothForms.opAt_add R τ)
    (GlobalTheory.SmoothForms.opAt_smul R τ) (GlobalTheory.SmoothForms.opAt_bracket R τ)).1
  have e : SmFun θ V = GlobalTheory.SmoothForms.SmF θ V := Submodule.ext fun φ => GlobalTheory.SmoothForms.smooth_iff R φ
  let E := (LinearEquiv.ofEq _ _ e).conjAlgEquiv ℂ
  have k : ∀ a b, E (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ (Matrix.single a b 1)) =
      GlobalTheory.SmoothForms.opInf R (atPlace V τ (P a b)) + Complex.I • GlobalTheory.SmoothForms.opInf R (atPlace V τ (Q a b)) := by
    intro a b
    refine LinearMap.ext fun φ => Subtype.ext ?_
    change RderC θ V τ (Matrix.single a b 1) φ.1 = _
    rw [RderC, conjAt, ← (hPQ _ _).1, ← (hPQ _ _).2, GlobalTheory.SmoothForms.Rder_eq R, GlobalTheory.SmoothForms.Rder_eq R]
    rfl
  intro a b c d
  apply E.injective
  have := hG a b c d
  simp only [← k] at this
  simp only [map_sub, map_mul, this, apply_ite E, map_zero]

end GlobalTheory.Mem.Lift

end
