import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.LatFin

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.MomT.LatFin.per_lattice_facts : ∀ (X : _root_.Formalism.L2.Col.Fields) (A : _root_.Formalism.L2.Ker.Amb X) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E b)),
    A.AA.FG → A.AA ≠ ⊥ → _root_.Formalism.L2.Col.IsSdLat N → _root_.Formalism.L2.Col.IsSdLat N' → (_root_.GlobalTheory.MomT.per A N N').FG ∧
    (∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N') ∧
    (∀ r : 𝓞 X.E, r ≠ 0 → (_root_.GlobalTheory.MomT.smulLat (r : X.E)
      (_root_.GlobalTheory.MomT.per A N N')).toAddSubgroup.relIndex
        (_root_.GlobalTheory.MomT.per A N N').toAddSubgroup ≠ 0) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A.AA =
      _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : _root_.Formalism.L2.Col.HomE X.E a b,
      y ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (_root_.GlobalTheory.MomT.per A N N') ↔
        ∀ v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, y v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  intro X A a b N N' hAfg hA hN hN'
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨hN'l, -⟩ := hN'
  have hfull : _root_.GlobalTheory.ThetaMove.Full (_root_.Formalism.L2.Ker.perO A.AA N N') :=
    _root_.GlobalTheory.ThetaMove.PeriodComp.full A.AA N N' hNl.fg hN'l hA
  have hfg : (_root_.GlobalTheory.MomT.per A N N').FG :=
    _root_.GlobalTheory.ThetaMove.VolumePos.perO_fg hAfg
      (_root_.GlobalTheory.ThetaMove.VolumePos.homO_fg hNl.fg hN'l.fg hNl.span_eq_top)
  have hmult : ∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧
      (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N' := by
    intro x
    obtain ⟨n, hn, hx⟩ := hfull x
    refine ⟨n, hn, ?_⟩
    unfold _root_.GlobalTheory.MomT.per
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hx
  refine ⟨hfg, hmult, ?_, ?_⟩
  · intro r hr
    refine _root_.GlobalTheory.ThetaMove.VolumePos.relIndex_ne_zero ?_ hfg
    intro x
    obtain ⟨n, hn, hx⟩ := hmult ((r : X.E)⁻¹ • x)
    refine ⟨n, hn, ?_⟩
    rw [_root_.GlobalTheory.MomT.mem_smulLat]
    refine ⟨_, hx, ?_⟩
    have hr' : (r : X.E) ≠ 0 := by exact_mod_cast hr
    rw [smul_smul, smul_smul, mul_comm (r : X.E), mul_assoc, mul_inv_cancel₀ hr', mul_one,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · intro P hP y
    unfold _root_.GlobalTheory.MomT.per
    constructor
    · intro hy v hv
      obtain ⟨s, hs, hsy⟩ := (_root_.Formalism.L2.Col.mem_locP P _ y).mp hy
      refine _root_.GlobalTheory.MomT.IdxBound.mem_localization_of_smul_mem P N' hs ?_
      simpa using _root_.GlobalTheory.MomT.IdxBound.per_apply_mem hP hsy hv
    · intro hy
      exact _root_.GlobalTheory.MomT.IdxBound.mem_localization_perO hP hNl.fg fun v hv =>
        hy v (_root_.GlobalTheory.ThetaMove.mem_localization_of_mem P hv)

end GlobalTheory.MomT.LatFin
