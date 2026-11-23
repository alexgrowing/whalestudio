import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalFactorUnitary

variable {D : D7}

theorem actO_gAt_of_wAt_eq_zero (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : wAt p u = 0) : actO S T (gAt S p g) (gAt T p h) u = u := by
  obtain ⟨hsplit, hcomm⟩ := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g h u
  have hz : idem D p • actO S T g h u = 0 := by
    rw [← wAt_eq_smul, hcomm, hu]
    unfold actO
    simp
  have hrest : (1 - idem D p) • u = u := by
    rw [sub_smul, one_smul, ← wAt_eq_smul, hu, sub_zero]
  rw [hsplit, hz, hrest, zero_add]

theorem compAt_mt_gAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : Place D) (g : GA D V) (τ : D.what₂.Tau)
    (hτ : Sum.inr τ ≠ p) : compAt θ τ (Formalism.L2.Theta.mt V (gAt V p g)) = 1 := by
  have h0 : (θ τ) ((infPart D) (idem D p)) = 0 := by
    obtain ⟨-, -, -, hfin, -, -, hinf⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
    rcases p with v | τ'
    · rw [(hfin v).1, map_zero]
    · have hne : τ' ≠ τ := fun e => hτ (by subst e; rfl)
      exact (hinf θ hθ τ).2 τ' hne
  unfold compAt
  rw [((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1 V p g).1]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
    map_one, h0, zero_mul, zero_add, sub_zero, one_mul]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLocal_om_gAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT hW hθ p f hf g h
  unfold IsLocal IsLatVac IsFockVacAt at hf ⊢
  obtain ⟨hth, ⟨hdbl, hhalf⟩, hfock⟩ := hf
  have hoff : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun v => Sum.inl v ≠ p), wAt p u = 0 := fun u hu =>
    (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 (fun _ hv => hv)
  refine ⟨hW.om_pres _ f hth, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have hw2 : wAt p (2 • u) = 0 := by
      rw [wAt_eq_smul, smul_comm, ← wAt_eq_smul, hoff u hu, smul_zero]
    have key := hW.om_heis (gAt S p g) (gAt T p h) (2 • u) f hth
    rw [hdbl u hu, actO_gAt_of_wAt_eq_zero S T p g h (2 • u) hw2] at key
    exact key.symm
  · intro e he u hu hu'
    have key := hW.om_heis (gAt S p g) (gAt T p h) u f hth
    rw [hhalf e he u hu hu', actO_gAt_of_wAt_eq_zero S T p g h u (hoff u hu)] at key
    exact key.symm
  · intro τ hτ z
    have hT1 : compAt θ τ (Formalism.L2.Theta.mt T (gAt T p h)) = 1 := compAt_mt_gAt hθ T p h τ hτ
    have hS1 : compAt θ τ (Formalism.L2.Theta.mt S (gAt S p g)⁻¹) = 1 := by
      rw [← gAt_inv]
      exact compAt_mt_gAt hθ S p g⁻¹ τ hτ
    have e1 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ z hth
    have e2 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ (cplxO (sS τ) (sT τ) z) hth
    rw [hT1, hS1, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have hz := hfock τ hτ z
    unfold annih at hz ⊢
    rw [← e1, ← e2, ← map_smul, ← map_add, hz, map_zero]

end GlobalTheory.LocalFactorUnitary
