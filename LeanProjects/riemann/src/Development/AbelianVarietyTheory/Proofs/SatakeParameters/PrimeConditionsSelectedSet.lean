import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.prime_conditions_selected_set : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → (∀ P : rowSG Pr sel mu, (qOf P.1).Prime ∧ ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) ∧ Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) ∧ ∀ u : Pr.Word, Disjoint (Pr.vT u) (rowSG Pr sel mu) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr R Ch sel S mu cst hX hPr hsel hg hT
  have nat : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ), (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := fun P n => by
    rw [mem_conjP, map_natCast]
  have hTm : ∀ u, ∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal := fun u P hP =>
    hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ ((GlobalTheory.MuOffMove.mem_vT hPr u P).1 hP)
  have hGm : ∀ P ∈ Pr.vGs, ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := fun P hP => by
    obtain ⟨i, hi⟩ := GlobalTheory.NormOneUnit.mem_vGs hP
    exact ⟨i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ hi⟩
  refine ⟨fun P => (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1,
    GlobalTheory.NormOneUnit.disjoint_vGs_QE mu hPr hsel hg, fun u => ⟨?_, fun P hP hP' => ?_⟩⟩
  · exact Finset.disjoint_left.2 fun P h h' => GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h' (hTm u P h)
  · rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
    · exact GlobalTheory.MuOffMove.conjP_notMem_vT hPr h h'
    · exact GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h' ((nat P _).2 (hTm u P h))
    · exact GlobalTheory.MuOffMove.level_notMem_rowSG hPr hsel (hT u) h ((nat P _).1 (hTm u _ h'))
    · rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
      · exact GlobalTheory.NormOneUnit.conjP_notMem_vGs hPr h h'
      · obtain ⟨i, hi⟩ := hGm P h
        exact GlobalTheory.MuOffMove.notMem_of_mem_QE hsel h' (hPr.g_prime i) (hg i) ((nat P _).2 hi)
      · obtain ⟨i, hi⟩ := hGm _ h'
        exact GlobalTheory.MuOffMove.notMem_of_mem_QE hsel h (hPr.g_prime i) (hg i) ((nat P _).1 hi)
      · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'
