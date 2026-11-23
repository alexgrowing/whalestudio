import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatVecSum

theorem princ_levJ_le_levLam_eq : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ, ∀ (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ),
      (((GlobalTheory.FlatVecSum.princ B).levLam ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((B.levLam ψ ⟨k, hle hk⟩ : ℂˣ) : ℂ) := by
  intro D S T B _ ψ _
  have hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ := by
    intro k hk
    obtain ⟨h1, h2⟩ := hk
    refine ⟨h1, ?_⟩
    have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
    rw [Subgroup.mem_bot.1 h2']
    exact Subgroup.one_mem _
  refine ⟨hle, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hk
  have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
  have e := Subgroup.mem_bot.1 h2'
  show ((Formalism.L2.DIV.levFn B.F.βS ((GlobalTheory.FlatVecSum.princ B).levS ψ) _ : ℂˣ) : ℂ) =
    ((Formalism.L2.DIV.levFn B.F.βS (B.levS ψ) _ : ℂˣ) : ℂ)
  unfold Formalism.L2.DIV.levFn
  congr 2
  · congr 1
    · show Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ))
          (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _) = Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _)
      have key : ∀ y, y = Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) ((Formalism.UG.bc (Lev.swapAE D)) ((finHom S).range.subtype k)) →
          Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ)) y =
            Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi y := by
        rintro y rfl
        rw [e]
        exact (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ (1 : _ →* ℂˣ)).trans (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one B.G.P.H B.G.P.chi).symm
      exact key _ rfl

end GlobalTheory.FlatVecSum
