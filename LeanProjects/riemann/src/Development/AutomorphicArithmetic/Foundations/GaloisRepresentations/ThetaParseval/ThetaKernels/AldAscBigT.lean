import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald.Asc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.SiegelWeilFormula.Ald.Asc
namespace PositivityTheory.SiegelWeilFormula.Ald
open Asc in
theorem bigT_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k := by
  intro hT _hA F E _ _ _ _ _ σ d dd0 had hrat
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ
    (Fin d.m × Fin d.n × Fin 2) _ d.dd dd0 (by exact d.ok.dbl.rat) (by exact hrat)
  have hop := hS.1
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = dd0.rho d.B.ψ w (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ]
    simp
  have rhoS' : ∀ w, ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), S0' (dd0.rho d.B.ψ w φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm (Fin d.m × Fin d.n × Fin 2) := hop.adm' d.l d.ok.dbl.adm
  have hsurj : ∀ y : Fin d.m × Fin d.n × Fin 2 → AF F, ∃ Z : Mx F E d.m d.n,
      dd0.e (Z * (incM F d.b.1.toCols₁)ᵀ) = (0, y) := by
    intro y
    obtain ⟨Z, X, hw⟩ := eq_split d.b (dd0.e.symm (0, y))
    have h1 := had Z X
    rw [← hw, LinearEquiv.apply_symm_apply] at h1
    have h2 := had Z 0
    rw [Matrix.zero_mul, add_zero, crdB_zero] at h2
    refine ⟨Z, h2.trans ?_⟩
    have h3 := congrArg Prod.snd h1
    simp only at h3
    rw [← h3]
  obtain ⟨t, ht0⟩ := d.ok.frame.2
  have ht : (d.b.1.toCols₁ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * (t.1 : Matrix (Fin d.n) (Fin d.n) E) := ht0
  have hinv : ∀ (y : Fin d.m × Fin d.n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2),
      l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨Z, hZ⟩ := hsurj y
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = dd0.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) φ := by
      funext x
      simp [Darboux.rho, hZ, schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    have e2 : Z * (incM F d.b.1.toCols₁)ᵀ = ((Z * (incM F t.1)ᵀ : Mx F E d.m d.n)) *
        ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)))ᵀ := by
      rw [ht, incM_mul', incM_diagCols, Matrix.transpose_mul]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [e2]
    exact d.ok.dbl.kill _ _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin d.n × Fin 2) l' hadm hinv
  have hform : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = c * S0 Φ (crdB d.bs X) := by
    intro Φ hΦ X
    have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ hΦ
    have h0 := had 0 X
    rw [Matrix.zero_mul, zero_add] at h0
    simp only [Bf_zero_left] at h0
    have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
      rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
      rfl
    rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ]
    simp [Darboux.rho, h0, schr]
  refine ⟨S0, S0', c, ?_, hS, hform⟩
  rintro rfl
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hz : d.T φ = 0 := by
    funext X
    rw [hform φ hφ X, zero_mul]
    rfl
  exact hφ0 (by rw [(hT.1 F E σ d).2.2 φ hφ hz]; rfl)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
