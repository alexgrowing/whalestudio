import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseLevelDatumLevelEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTraceChiCol

open Classical in

def colLam {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : ℂ :=
  if h : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal then
    Formalism.L2.Forms.lamJ (T.gl.psi0 h.choose v h.choose_spec) (T.gl.chiB h.choose v h.choose_spec) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
        (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g)))
  else 1

theorem type_idx_unique {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {j j' : Fin 2}
    (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal) : j' = j := by
  by_contra hne
  have hg : D.host.g j' ≠ D.host.g j := by
    intro e
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      subst hj hj' <;> first | exact hne rfl | exact D.host.g_ne e | exact D.host.g_ne e.symm
  have hc : Nat.Coprime (D.host.g j') (D.host.g j) := (Nat.coprime_primes (D.host.g_prime j') (D.host.g_prime j)).2 hg
  obtain ⟨a, b, hab⟩ : IsCoprime (D.host.g j' : ℤ) (D.host.g j : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (1 : 𝓞 D.host.F) ∈ v.asIdeal := by
    have e : ((a * (D.host.g j' : ℤ) + b * (D.host.g j : ℤ) : ℤ) : 𝓞 D.host.F) = 1 := by rw [hab]; simp
    rw [← e]
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h') (v.asIdeal.mul_mem_left _ h)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem colLam_eq {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)}
    (j : Fin 2) (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal)
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    colLam T v g = Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
  have hex : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := ⟨j, h⟩
  unfold colLam
  rw [dif_pos hex]
  have key : ∀ (j' : Fin 2) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal), j' = j →
      Formalism.L2.Forms.lamJ (T.gl.psi0 j' v h') (T.gl.chiB j' v h') D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j' v h' (T.glev0.fr j' v h') (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) =
      Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
    rintro j' h' rfl; rfl
  exact key _ _ (type_idx_unique h hex.choose_spec)

end GlobalTheory.FamTraceChiCol

end
