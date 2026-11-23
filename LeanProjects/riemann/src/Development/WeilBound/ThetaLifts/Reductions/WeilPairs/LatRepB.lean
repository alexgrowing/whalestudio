import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integral_trace_one (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ w : 𝓞 E, w + sgOF σ w = 1 :=
  LatB.exists_w hB.cm hB.unram

theorem exists_good_norm_character (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  haveI := hB.galois
  exact LatB.exists_goodNorm hB.cm hB.unram

theorem lattice_stable_under_idempotents (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ := by
  intro e he a ha
  obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
  exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

theorem lattice_index_prime_to_inert (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) :=
  LatB.idx_main hB.cm hfin

end PositivityTheory.ThKW

end
