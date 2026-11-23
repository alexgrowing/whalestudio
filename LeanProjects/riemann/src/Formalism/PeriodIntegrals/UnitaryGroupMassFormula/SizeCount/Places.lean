import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.TauPlBijective

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem eTau_tauPl (D : D7) (z : Bool × HH D) :
    (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold Formalism.BasicNotions.tauPl
  simp

theorem ramifiedTau1_ne_ramifiedTau2 (φ : Formalism.HC.Frame) (a b : φ.A) : φ.tau1 a ≠ φ.tau2 b := by
  intro h
  have h1 := congrArg (fun x => x.1.1) h
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  revert h1
  decide

theorem tau1_injective_alt (φ : Formalism.HC.Frame) {a b : φ.A} (h : φ.tau1 a = φ.tau1 b) : a = b := by
  simp only [Formalism.HC.Frame.tau1, Prod.mk.injEq, true_and] at h
  simpa [Formalism.HC.Frame.iota] using h

theorem placeFacts : PlaceFacts := by
  intro D
  have h1 : ∀ t : HH D, (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have h2 : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) = D.R.tau2 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have hPsi : ∀ z : Bool × HH D, (D.eTau (tauPl D z) : D.R.GG) ∈ D.R.Psi :=
    fun z => (D.eTau (tauPl D z)).2
  have hnt : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces := by
    intro t h
    rw [h2] at h
    unfold Host.topPlaces at h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha
  refine ⟨h1, ?_, hnt, ?_⟩
  · intro t ht
    refine ⟨hPsi _, ?_, ?_⟩
    · intro h
      rw [h1] at h
      unfold Host.topPlaces at h
      obtain ⟨a, ha, hat⟩ := Finset.mem_image.1 h
      exact ht (tau1_injective_alt _ hat ▸ ha)
    · intro h
      rw [h1] at h
      unfold Host.thickPlaces at h
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
      exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha.symm
  · intro t
    by_cases h : (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inl h
    · exact Or.inr ⟨hPsi _, hnt t, h⟩

end PI.SzCt.UnitaryGroupMassFormula
