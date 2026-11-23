import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem normRepMove_of_steps (D : D7) (u u' : D.what₂.Word) (hE : TermEqIff D u u')
    (h1 : StepExp D) (h2 : StepGram D) (h3 : StepGlob D) (h4 : StepLoc D) (h5 : StepTr D) :
    PI.NormRepChange.NormRepMove D u u' := by
  intro F0 Λ hΛ t _hrel F₁ F₂ hR1 hA1 hR2 hA2 w _hw
  obtain ⟨p1, e1⟩ := hR1
  obtain ⟨p2, e2⟩ := hR2
  have hDC : DCRel Λ (lf D F0) F₁ F₂ :=
    ((hE F0 Λ hΛ) ⟨F₁, p1⟩ ⟨F₂, p2⟩).mp (e1.trans e2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hDC
  obtain ⟨hNu, hNe⟩ := h1 Λ (lf D F0) n hn
  obtain ⟨hMu, hMe⟩ := h1 Λ F₁ m hm
  have hG := h2 (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hNe hMe hfr
  obtain ⟨A, B, hA, hB, hZ, hs⟩ := core_Z _ _ _ _ hNu hMu hG
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  rw [hs]
  obtain ⟨_, ⟨_, _, hLift0, hConv0⟩, hXS0⟩ := hΛ
  obtain ⟨hLift1, _, hConv1, hXS1⟩ := p1
  have hglob : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E,
      (o : D.host.E) = (sgUp (fmat D (lf D F0) n) + sgUp (fmat D F₁ m)) * δ := by
    intro δ hδ
    obtain ⟨o1, ho1⟩ := h3 Λ (lf D F0) n hn hXS0 hLift0.1 δ hδ
    obtain ⟨o2, ho2⟩ := h3 Λ F₁ m hm hXS1 hLift1.1 δ hδ
    exact ⟨o1 + o2, by rw [add_mul, ← ho1, ← ho2]; norm_cast⟩
  have hloc := h4 Λ (lf D F0) F₁ F₂ n m hn hm hfr hConv0 hConv1 hA1 hA2 hLift0.1 hLift1.1
  obtain ⟨k, hk⟩ := h5 _ hglob hloc
  exact psiInf_of_trace (gS D) _ _ k hk

end PI.NRCW
