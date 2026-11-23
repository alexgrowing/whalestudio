import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartitionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

theorem evG_id_smul {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (a : ℂ) (P : Pol ℂ ι n) :
    evG fr sh (RingHom.id ℂ) (a • P) = a • evG fr sh (RingHom.id ℂ) P := by
  funext y
  simp only [evG, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply]
  ring

theorem Kmap_isVal : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi hU c c' f hf
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨n, h1, h2, h3, h4⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hle : D.R.N i ≤ D.R.N (i + 1) := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have key := GlobalTheory.KerWt.tied_on_models D u C O i hi (nuT D u i) hU ℂ (RingHom.id ℂ) (lamTG M i) n h1 c c'
    (jetC O.dgen (O.Th i c c')) 1 (fun m => by simp) (fun τ => (lamTG M i τ).detShift) h2 P hP
  rw [one_smul] at key
  have hsh : (fun τ => -C.sDiv i τ) = fun τ => (lamTG M (i + 1) τ).detShift := funext fun τ => (h4 τ).symm
  rw [hsh] at key
  refine ⟨(C.rhoDet i c * C.rhoDet' i c') • jetMap (jetC O.dgen (O.Th i c c')) n P, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (GlobalTheory.KerWt.jet_in_vv_of_weight ℂ D.what₂.Tau _ _ hle (lamTG M i) (lamTG M (i + 1)) n h3 _ P hP)
  · rw [key, evG_id_smul]

end GlobalTheory.KerJ
