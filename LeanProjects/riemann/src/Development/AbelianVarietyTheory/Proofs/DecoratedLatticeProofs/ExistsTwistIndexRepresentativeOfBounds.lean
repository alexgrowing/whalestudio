import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.MRepsPick

theorem exists_rep_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ j c h γ hγ hal hne
  classical
  obtain ⟨b₀⟩ := hne
  have hj : j < s := by omega
  let hh : rowSG Pr sel mu → AutY X R (j + 1) := fun P' => if P' = P then γ else L.h (j + 1) b₀ P'
  obtain ⟨b, hb⟩ := hL.surj j hj hh
    (by
      intro P' hP'
      have hne : P' ≠ P := by
        rintro rfl
        exact hA.nmem hP'
      simp only [hh, if_neg hne]
      exact hL.stabG (j + 1) b₀ P' hP')
    (by
      intro P' hP'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, if_pos rfl]
        exact hγ
      · simp only [hh, if_neg hPP]
        exact hL.boundQ (j + 1) b₀ P' hP')
    (by
      intro P'
      by_cases hPP : P' = P
      · subst hPP
        simp only [hh, if_pos rfl]
        exact hal
      · simp only [hh, if_neg hPP]
        exact hL.nonvan j hj b₀ P')
  refine ⟨b, ?_⟩
  have := hb P
  simpa [hh] using this

end GlobalTheory.MRepsPick
