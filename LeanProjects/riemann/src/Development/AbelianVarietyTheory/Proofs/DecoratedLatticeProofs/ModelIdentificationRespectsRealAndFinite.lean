import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.SeeReal

variable {D : D7}

theorem isAtTau_atTau (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau θ V τ g (atTau θ V τ g) := by
  have hex := (Formalism.IndefR.Eqv.atTauExUnique_holds D θ hθ V τ g hg).exists
  unfold atTau
  rw [dif_pos hex]
  exact hex.choose_spec

theorem eq_of_conj {n : ℕ} {P A B : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (e : P * A * P⁻¹ = B) :
    A = P⁻¹ * B * P := by
  rw [← e]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left P A hP]

theorem phi_inst (v : InfinitePlace D.host.F) (x : D.host.E) :
    (Formalism.IndefR.RationalEmbedding.inst D).φ v x = embS D ((Formalism.L2.Host.tauPl D).symm v) x := rfl

theorem realSplit_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 = 1) ∧
    (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).2 = 1) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      (∀ v, v ≠ pl.symm τ → ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
      HEq (uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ)))
        ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
          ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
    ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  subst h
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (phi_inst v x))
  subst hpl
  have hT : ∀ k, ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := fun _ => rfl
  have hP : ∀ v, IsUnit ((Formalism.IndefR.RationalEmbedding.inst D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)
  refine ⟨fun k => ?_, fun k => ?_, fun τ g hg => ?_, fun τ y => ?_⟩
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · have hg' : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ := hg
    have hk := isAtTau_atTau (Formalism.IndefR.Eqv.thetaC D) (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hg'
    rw [hT]
    generalize atTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g = k at hk ⊢
    obtain ⟨x, rfl⟩ := (Formalism.IndefR.RationalEmbedding.iota D).symm.surjective k
    rw [ContinuousMulEquiv.apply_symm_apply]
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x
    refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x).1 hk.1, fun v hv => ?_, heq_of_eq ?_⟩
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hρ : ρ ≠ τ := fun e => hv (by rw [e]; rfl)
      have e0 : Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ) * Formalism.L2.SG.EvalTIota.uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ))⁻¹ = (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ) := by
        rw [← hbr ρ, hk.2.2 ρ hρ]
      have e1 := eq_of_conj (hP _) e0
      simp only [Formalism.L2.SG.EvalTIota.Pi, Formalism.L2.SG.EvalTIota.uM'] at e1
      have e2 : uMat (x.1 (Formalism.L2.Host.tauPl D ρ)) = 1 := by
        rw [e1]
        erw [Matrix.mul_one]
        exact Matrix.nonsing_inv_mul _ (hP _)
      exact Subtype.ext (Units.ext e2)
    · exact eq_of_conj (hP _) ((hbr τ).symm.trans hk.2.1)
  · classical
    let x0 : (Formalism.IndefR.RationalEmbedding.inst D).GA :=
      (Pi.mulSingle (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y, 1)
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x0
    let g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
      (Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ) * uMat y * ((Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ))⁻¹
    have hk0 : IsAtTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g ((Formalism.IndefR.RationalEmbedding.iota D).symm x0) := by
      refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x0).2 rfl, ?_, fun ρ hρ => ?_⟩
      · rw [hbr τ]
        have hy : x0.1 (Formalism.L2.Host.tauPl D τ) = y :=
          Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y
        have hy' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D τ) = uMat y := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D τ)) = uMat y
          rw [hy]
        rw [hy']
        rfl
      · rw [hbr ρ]
        have hne : Formalism.L2.Host.tauPl D ρ ≠ Formalism.L2.Host.tauPl D τ := (Formalism.L2.Host.tauPl D).injective.ne hρ
        have h1 : x0.1 (Formalism.L2.Host.tauPl D ρ) = 1 := Pi.mulSingle_eq_of_ne hne _
        have h1' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D ρ) = 1 := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D ρ)) = 1
          rw [h1]
          rfl
        rw [h1']
        erw [Matrix.mul_one]
        exact Matrix.mul_nonsing_inv _ (hP _)
    have hgU : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ :=
      Formalism.IndefR.Eqv.atTauUnitary_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g _ hk0
    refine ⟨g, hgU, ?_⟩
    have hu := (Formalism.IndefR.Eqv.atTauExUnique_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU).unique
      (isAtTau_atTau _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU) hk0
    rw [hT, hu, ContinuousMulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) _ _

theorem realSplit_of_idE : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ :=
  fun _ X h θ hθ hE => realSplit_gen h X.ιE hE X.pl X.φ_eq θ hθ

end GlobalTheory.Core.Mi.SeeReal
