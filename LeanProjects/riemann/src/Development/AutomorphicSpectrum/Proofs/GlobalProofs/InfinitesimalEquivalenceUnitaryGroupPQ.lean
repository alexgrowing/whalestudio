import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LocalPointData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.GelfandCentralHolds
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.PCDense

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GKClosure

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem dsigC_mem_sub (hV : IsGKSub ε ρ V) (Y : Matrix (Fin n) (Fin n) ℂ) {v : H} (hv : v ∈ V) :
    PI.DSInfCharCap.dsigC ε ρ Y v ∈ V := by
  rw [dsigC_eq]
  exact add_mem (hV.lieStable _ (cre_mem Y) v hv) (Submodule.smul_mem _ _ (hV.lieStable _ (cim_mem Y) v hv))

def vAct (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V where
  toFun Y :=
    { toFun := fun v => ⟨PI.DSInfCharCap.dsigC ε ρ Y v, dsigC_mem_sub hV Y v.2⟩
      map_add' := fun v w => Subtype.ext (dsigC_add_vec (hV.smooth v v.2) (hV.smooth w w.2) Y)
      map_smul' := fun c v => Subtype.ext (dsigC_smul_vec (hV.smooth v v.2) Y c) }
  map_add' Y Z := LinearMap.ext fun v => Subtype.ext (dsigC_add hρ (hV.smooth v v.2) Y Z)
  map_smul' c Y := LinearMap.ext fun v => Subtype.ext (dsigC_smul hρ (hV.smooth v v.2) c Y)

def vE (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ V) (a b : Fin n) : Module.End ℂ V :=
  vAct hρ hV (single a b 1)

def vIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (Λ : Fin n → ℝ) :
    Submodule ℂ H :=
  sSup {S | S ≤ V ∧ IsKTypeOf ε ρ Λ S}

def vK (hV : IsGKSub ε ρ V) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) : Module.End ℂ V :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

section Equiv

variable [CompleteSpace H]

theorem isGKSub_kFinVec (hU : IsURepOn (UJset ε) ρ) (hI : IsIrredOn (UJset ε) ρ) :
    IsGKSub ε ρ (kFinVec ε ρ) := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H ρ hU hI
  exact ⟨fun v hv => CompanionTheory.D.gk.HC.smoothVec_of_smD_A (h1 v hv), fun v hv => hv, isKStableOn_kFinVec ε ρ,
    fun X hX v hv => GlobalTheory.CompanionTheory.KFinLink.isLieStable_of hU hI X hX v hv⟩

end Equiv

section Two

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

end Two

end GlobalTheory.CompanionTheory.GKClosure

namespace GlobalTheory.CompanionTheory.Published

end GlobalTheory.CompanionTheory.Published

end
