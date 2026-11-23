import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddSingle

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open GlobalTheory.CompanionTheory.ModelS.FFin in

theorem GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ)
    (hlev : IsLev lam lev) (F : GlobalTheory.CompanionTheory.ModelS.SmF n) (hF : F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev) :
    ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧
      ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  obtain ⟨m, p, hp⟩ := fRaw_factor lam hl lev hlev
  set e := GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev) with he
  have hfin : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree) := inferInstance
  refine ⟨(MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree).map (wfL e m), inferInstance,
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩, ?_⟩
  · apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · show wf e m p g = F.1 g
      rw [hF, hp g hg, wf, Set.indicator_of_mem hg]
    · show wf e m p g = F.1 g
      rw [wf, Set.indicator_of_notMem hg, F.2.2 g hg]
  · rintro a b _ ⟨q, hq, rfl⟩
    refine ⟨(if a = b then (m : ℂ) else 0) • q + Tp a b q,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hq) (Tp_mem a b _ hq), ?_⟩
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · rw [Kf_wf e m q (wfL e m q) rfl a b hg]
      show wf e m _ g = _
      rw [wf, Set.indicator_of_mem hg, evalPoints_add, evalEmbedding_smul]
    · show wf e m _ g = _
      rw [wf, Set.indicator_of_notMem hg, (GlobalTheory.CompanionTheory.ModelS.Kf a b (wfL e m q)).2.2 g hg]
