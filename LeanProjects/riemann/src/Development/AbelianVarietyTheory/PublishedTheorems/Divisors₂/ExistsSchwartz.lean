import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published.ThetaConvModel

variable {D : D7}

theorem exists_schwartz (θ : InfFam D) (m n : ℕ) : ∃ Φ : schwartzA θ m n, Φ.1 0 ≠ 0 := by
  classical
  let b : ContDiffBump (0 : D.what₂.Tau → Fin m → Fin n → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := hb1.toSchwartzMap hb2
  have hf : f 0 = 1 := by
    show ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; simp
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ Formalism.L2.Theta.intAE D}
      add_mem' := fun ha hb i j => (Formalism.L2.Theta.intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (Formalism.L2.Theta.intAE D).zero_mem
      neg_mem' := fun ha i j => (Formalism.L2.Theta.intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (Formalism.L2.Theta.intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D m n → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ m n := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show f _ * g _ ≠ 0
  have e : (fun τ i j => compAt θ τ (0 : Mx D m n) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := by
    ext τ i j; simp [compAt]
  rw [e, hf]
  simp [g]
  exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin m) (Fin n) _)).2 W.zero_mem

theorem le_absThetaInt (V : HSp D) (ν : Measure (GA D V)) {n : ℕ} (φ : Mx D V.rank n → ℂ) :
    ‖φ 0‖ₑ * autMeasure V ν Set.univ ≤ absThetaInt V ν φ := by
  rw [← lintegral_const]
  refine lintegral_mono fun q => ?_
  have h := ENNReal.le_tsum (f := fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖φ (invPt V q.out ξ)‖ₑ) 0
  have e : invPt V q.out (0 : Matrix (Fin V.rank) (Fin n) D.host.E) = 0 := by
    simp [invPt]
  rw [e] at h
  exact h

theorem absThetaInt_pos (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {n : ℕ} (φ : Mx D V.rank n → ℂ)
    (h : φ 0 ≠ 0) : 0 < absThetaInt V ν φ :=
  lt_of_lt_of_le (ENNReal.mul_pos (by simpa using h) (NeZero.ne _)) (le_absThetaInt V ν φ)

theorem absThetaInt_one (V : HSp D) (hV : 1 ≤ V.rank) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {n : ℕ} (hn : 1 ≤ n) :
    absThetaInt V ν (fun _ : Mx D V.rank n => (1 : ℂ)) = ⊤ := by
  haveI : Infinite (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    Infinite.of_surjective (fun x => x ⟨0, hV⟩ ⟨0, hn⟩) fun a => ⟨fun _ _ => a, rfl⟩
  have h3 : descend (GQ V) (absTheta V (fun _ : Mx D V.rank n => (1 : ℂ))) = fun _ => ⊤ := funext fun q => by
    rw [AutomorphicL2Unitary.descend, absTheta]
    simp
  rw [absThetaInt, h3, lintegral_const, ENNReal.top_mul (NeZero.ne _)]

theorem rank_zero (V : HSp D) (hV : V.rank = 0) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {n : ℕ} (φ : Mx D V.rank n → ℂ) :
    absThetaInt V ν φ < ⊤ := by
  have : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h3 : descend (GQ V) (absTheta V φ) = fun _ => ‖φ 0‖ₑ := funext fun q => by
    have hs : Subsingleton (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun x y => Matrix.ext fun i => isEmptyElim i⟩
    rw [AutomorphicL2Unitary.descend, absTheta, tsum_eq_single 0 fun b hb => (hb (Subsingleton.elim _ _)).elim]
    exact congrArg (fun z => ‖φ z‖ₑ) (Matrix.ext fun i => isEmptyElim i)
  rw [absThetaInt, h3, lintegral_const]
  exact ENNReal.mul_lt_top enorm_lt_top (measure_lt_top _ _)

theorem instances (H : GlobalTheory.Published.WeilThetaConvergence) (D : D7) (n : ℕ) (hn : 1 ≤ n) :
    (∃ (θ : InfFam D) (Φ : schwartzA θ (pos D 1).rank n), IsInfFam θ ∧
      0 < absThetaInt (pos D 1) Measure.haar Φ.1 ∧ absThetaInt (pos D 1) Measure.haar Φ.1 < ⊤) ∧
    (∃ (θ : InfFam D) (Φ : schwartzA θ (dblSp (pos D 2)).rank 1), IsInfFam θ ∧ Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D 2)) = 2 ∧
      0 < absThetaInt (dblSp (pos D 2)) Measure.haar Φ.1 ∧ absThetaInt (dblSp (pos D 2)) Measure.haar Φ.1 < ⊤) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨Φ, hΦ⟩ := exists_schwartz θ (pos D 1).rank n
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz θ (dblSp (pos D 2)).rank 1
  refine ⟨⟨θ, Φ, hθ, absThetaInt_pos _ _ _ hΦ, H D n _ hn (.inl (wittIdx_pos 1)) θ hθ _ inferInstance Φ⟩,
    ⟨θ, Ψ, hθ, wittIdx_dblSp _, absThetaInt_pos _ _ _ hΨ, H D 1 _ le_rfl (.inr ?_) θ hθ _ inferInstance Ψ⟩⟩
  rw [wittIdx_dblSp]; exact show 1 + 2 < 2 + 2 by decide

theorem split_excluded (D : D7) (k n : ℕ) (hk : 1 ≤ k) (h : k ≤ n) : ¬ (Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D k)) = 0 ∨
    n + Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D k)) < (dblSp (pos D k)).rank) := by
  rw [wittIdx_dblSp]
  show ¬ (k = 0 ∨ n + k < k + k)
  omega

end GlobalTheory.Published.ThetaConvModel

end
