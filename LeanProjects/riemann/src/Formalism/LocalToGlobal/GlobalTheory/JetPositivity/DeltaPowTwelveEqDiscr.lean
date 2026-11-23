import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

section Pieces

variable {R : Ranks} (host : Host R) {LL : Type} [Field LL] [NumberField LL] (embLL : LL →+* ℂ)
  {Tau : Type} [Fintype Tau] (eTau : Tau ≃ R.Psi)

def lamOfH (cc : Ideal (𝓞 host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * host.φ₀ (((c : host.K) : host.E))}

def embTH (τ : Tau) : host.E →+* ℂ := host.emb (eTau τ : R.GG)

def mmMH (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (Tau → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (host.AA0 : Submodule (𝓞 host.E) host.E),
    v = fun τ => TaylorLogMetric.liftM M (embTH host eTau τ a)}

def ellTH (M : IntermediateField ℚ ℂ) [NumberField M] (τ : Tau) : Submodule (𝓞 M) M :=
  (mmMH host eTau M).comap (LinearMap.single (𝓞 M) (fun _ : Tau => (M : Type)) τ)

def conjOfH {M : IntermediateField ℚ ℂ} (e : LL ≃+* M) (s : LL →+* ℂ) : M →ₐ[ℚ] ℂ :=
  (s.comp (e.symm : M →+* LL)).toRatAlgHom

structure CurveDat where
  δ : ℂ
  delta_pow_twelve_eq_discr : δ ^ 12 = TaylorLogMetric.discr (lamOfH host host.ccK 1)
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = embLL y
  fr : Tau → M
  fr_ne : ∀ τ, fr τ ≠ 0
  gen : ∀ τ, ellTH host eTau M τ = Submodule.span (𝓞 M) {fr τ}

attribute [instance] CurveDat.nf

variable {host embLL eTau}

def lamS (K : CurveDat host embLL eTau) (s : LL →+* ℂ) : AddSubgroup ℂ :=
  TaylorLogMetric.lamConj K.M (conjOfH K.eL s) (lamOfH host host.ccK K.δ)

def th0S (K : CurveDat host embLL eTau) (s : LL →+* ℂ) : ℂ → ℂ :=
  Classical.epsilon fun G => GlobalTheoryTheory.IsTheta0 host.d (lamS K s) G

def omVal (K : CurveDat host embLL eTau) (τ : Tau) (s : LL →+* ℂ) : ℝ :=
  (Real.pi * ‖conjOfH K.eL s (K.fr τ)‖ ^ 2 / TaylorLogMetric.area (lamS K s))⁻¹

def thOneVal (K : CurveDat host embLL eTau) (s : LL →+* ℂ) : ℝ :=
  Real.sqrt (GlobalTheoryTheory.normSq1 (lamS K s) (th0S K s))

def guardPos (x : ℝ) : ℝ := if 0 < x then x else 1

theorem guardPos_pos (x : ℝ) : 0 < guardPos x := by
  unfold guardPos; split_ifs with h
  · exact h
  · exact one_pos

theorem guardPos_of_pos {x : ℝ} (h : 0 < x) : guardPos x = x := if_pos h

def gxOf (K : CurveDat host embLL eTau) : GlobalExtra LL Tau where
  Om τ s := guardPos (omVal K τ s)
  Om_pos _ _ := guardPos_pos _
  thOne s := guardPos (thOneVal K s)
  thOne_pos _ := guardPos_pos _

end Pieces

end Formalism.L2.GlobalTheoryTheory.Jets
