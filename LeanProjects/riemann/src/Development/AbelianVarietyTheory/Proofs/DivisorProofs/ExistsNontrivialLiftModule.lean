import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockQuot

variable (P Q R S : ℕ)

def rel (x : ℚ) : Submodule ℂ (Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Pol P Q R S), g = fockAct1 P Q R S X f - ((x : ℂ) * X.trace) • f}

def act2 (t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S) :=
  fockAct2 P Q R S + (Matrix.traceLinearMap (Ix R S) ℂ ℂ).smulRight ((t : ℂ) • (1 : Module.End ℂ (Pol P Q R S)))

theorem fockSecondActionTraceShift_apply (t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    act2 P Q R S t Y f = fockAct2 P Q R S Y f + ((t : ℂ) * Y.trace) • f := by
  simp [act2, mul_comm, smul_smul]

theorem fockTraceCharacterRelations_le_comap_secondAction (x t : ℚ) (Y : Mat R S) : rel P Q R S x ≤ (rel P Q R S x).comap (act2 P Q R S t Y) := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨X, f, rfl⟩
  have hc : fockAct2 P Q R S Y (fockAct1 P Q R S X f) = fockAct1 P Q R S X (fockAct2 P Q R S Y f) :=
    (LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Y) f).symm
  refine Submodule.subset_span ⟨X, act2 P Q R S t Y f, ?_⟩
  simp only [fockSecondActionTraceShift_apply, map_sub, map_add, map_smul, hc]

theorem isLieAct_fockSecondActionTraceShift (t : ℚ) : IsLieAct (act2 P Q R S t) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, fockSecondActionTraceShift_apply, map_add, map_smul, h, Matrix.trace_sub,
    Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, add_zero]
  module

def actQ (x t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S ⧸ rel P Q R S x) where
  toFun Y := (rel P Q R S x).mapQ (rel P Q R S x) (act2 P Q R S t Y) (fockTraceCharacterRelations_le_comap_secondAction P Q R S x t Y)
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]

theorem actQ_mk (x t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    actQ P Q R S x t Y (Submodule.Quotient.mk f) = Submodule.Quotient.mk (act2 P Q R S t Y f) := rfl

theorem actQ_lie (x t : ℚ) : IsLieAct (actQ P Q R S x t) := by
  intro X Y
  refine LinearMap.ext fun v => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := LinearMap.congr_fun (isLieAct_fockSecondActionTraceShift P Q R S t X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  simp only [actQ_mk, h, Submodule.Quotient.mk_sub]

theorem actQ_kfin (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    ∃ W : Submodule ℂ (Pol P Q R S ⧸ rel P Q R S x), FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (actQ P Q R S x t) W := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  refine ⟨W₀.map (rel P Q R S x).mkQ, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
  rintro X hX _ ⟨w, hw, rfl⟩
  refine ⟨act2 P Q R S t X w, ?_, rfl⟩
  rw [fockSecondActionTraceShift_apply]
  exact W₀.add_mem (hst X hX w hw) (W₀.smul_mem _ hw)

theorem actQ_wt (x t : ℚ) (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈ wtSub (actQ P Q R S x t) (fun a => μ a + t) := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actQ_mk, fockSecondActionTraceShift_apply, hg a]
  simp [Eab, Matrix.trace_single_eq_same, add_smul]

theorem actQ_wts (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    v ∈ ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
  refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
    (motive := fun g => (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈
      ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ) hf ?_ ?_ ?_
  · intro μ g hg
    exact Submodule.mem_iSup_of_mem _ (actQ_wt P Q R S x t μ g hg)
  · simp
  · intro g h hg hh
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ hg hh

def gkQ (x t : ℚ) : GKMod R S where
  V := Pol P Q R S ⧸ rel P Q R S x
  act := actQ P Q R S x t
  lie := actQ_lie P Q R S x t
  kfin := actQ_kfin P Q R S x t
  wts := actQ_wts P Q R S x t

theorem mk_fockFirstAction_eq_trace_smul (x : ℚ) (X : Mat P Q) (f : Pol P Q R S) :
    (Submodule.Quotient.mk (fockAct1 P Q R S X f) : Pol P Q R S ⧸ rel P Q R S x) =
      ((x : ℂ) * X.trace) • Submodule.Quotient.mk f := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨X, f, rfl⟩

theorem nontrivial_of_form (x : ℚ) (l : Pol P Q R S →ₗ[ℂ] ℂ) (hl : l ≠ 0)
    (hlX : ∀ X f, l (fockAct1 P Q R S X f) = (x : ℂ) * X.trace * l f) : Nontrivial (Pol P Q R S ⧸ rel P Q R S x) := by
  have hK : rel P Q R S x ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨X, f, rfl⟩
    simp [hlX]
  obtain ⟨f, hf⟩ : ∃ f, l f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl (LinearMap.ext fun f => by simpa using h f)
  refine ⟨⟨Submodule.Quotient.mk f, 0, ?_⟩⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact fun hm => hf (hK hm)

theorem exists_lift : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x →
    ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V),
      GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := by
  intro P Q R S x t ⟨l, hl, hlX⟩
  refine ⟨gkQ P Q R S x t, (rel P Q R S x).mkQ, ⟨Submodule.mkQ_surjective _, ?_, ?_⟩, ?_⟩
  · intro X f
    exact mk_fockFirstAction_eq_trace_smul P Q R S x X f
  · intro Y f
    show actQ P Q R S x t Y (Submodule.Quotient.mk f) = _
    rw [actQ_mk, fockSecondActionTraceShift_apply]
    rfl
  · exact nontrivial_of_form P Q R S x l hl hlX

end GlobalTheory.FockQuot
