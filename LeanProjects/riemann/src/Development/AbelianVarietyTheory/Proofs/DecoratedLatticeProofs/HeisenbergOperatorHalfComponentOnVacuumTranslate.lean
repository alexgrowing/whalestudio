import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfAStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorFinitePartRestActsBySemicharacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) = alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm))) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 _ ΛS ΛT dS dT eS eT f₀ hV x' hx y' hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hV
  change heisO ψ S T ((LinearMap.toMatrix' x').map fun r => e * incA D r)
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀) =
    alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x'))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀)
  set Xt : WO S T := (LinearMap.toMatrix' x').map fun r => e * incA D r with hXt
  set FX := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x') with hFX
  set FY := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') with hFY
  set α := alV D.host.d sc (embH (tauE D) δ x') with hα
  have hact := GlobalTheory.T.heisenbergOperator_finitePartRest_acts_by_semicharacter D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP f₀ hV x' hx
  have hcomm := GlobalTheory.T.addChar_symplectic_finitePartRest_eq_one D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx y' hy
  have hcoc := GlobalTheory.T.halfA_idempotent_component_cocycle_trivial D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hsq := GlobalTheory.T.semicharacter_sq_eq_one_on_halfA D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hZ : heisO ψ S T (FX - Xt) (heisO ψ S T FY f₀) = α • heisO ψ S T FY f₀ := by
    rw [GlobalTheory.SplitScalar.heisO_comm, hcomm, one_smul, hact, GlobalTheory.SplitScalar.heisO_smul]
  have hX := GlobalTheory.SplitScalar.heisO_heisO ψ S T Xt (FX - Xt) (heisO ψ S T FY f₀)
  rw [hcoc, one_smul, add_sub_cancel, hZ, GlobalTheory.SplitScalar.heisO_smul] at hX
  rw [← hX, smul_smul, hsq, one_smul]
