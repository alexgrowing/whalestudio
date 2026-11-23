import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host NumberField IsDedekindDomain

def hcSigma {R : Ranks} (P : HCParam R) : Multiset ℂ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => ((P.v i : ℚ) : ℂ)) +
    (Finset.univ : Finset (Fin R.m)).val.map (fun j => -((P.b j : ℚ) : ℂ))

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := embPsi D.host (D.eTau τ)

def embTauBar (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := (starRingEnd ℂ).comp (embTau D τ)

def IsCuspParam (D : D7) (S : GlobalTheory.HeightCounting.RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧
  D.naut.ralg π ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → D.naut.locG π w = S.locR σ w) ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG π w)) ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
    D.naut.unr (D.naut.locG π w)) ∧
  (∀ τ : D.what₂.Tau, D.naut.infG π (embTau D τ) = hcSigma (D.hc τ) ∧
    D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z))

def GoodRowCuspParam (D : D7) (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ →
    ∃ π : D.naut.CG D.R.r, IsCuspParam D S σ π

theorem card_hcSigma {R : Ranks} (P : HCParam R) : Multiset.card (hcSigma P) = R.r := by
  have := R.m_add_three_le_k
  simp only [hcSigma, Multiset.card_add, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
    Ranks.r]
  omega

theorem hcSigma_int {R : Ranks} (P : HCParam R) : ∀ z ∈ hcSigma P, ∃ n : ℤ, z = (n : ℂ) := by
  intro z hz
  simp only [hcSigma, Multiset.mem_add, Multiset.mem_map] at hz
  rcases hz with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · obtain ⟨n, hn⟩ := P.v_int i
    exact ⟨n, by rw [hn]; simp⟩
  · obtain ⟨n, hn⟩ := P.b_int j
    exact ⟨-n, by rw [hn]; simp⟩

theorem IsCuspParam.unr {D : D7} {S : GlobalTheory.HeightCounting.RowSide D} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
    (h : IsCuspParam D S σ π) (w : PlE D.host) (hw : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) :
    D.naut.unr (D.naut.locG π w) := by
  by_cases hs : IsSplitPl D.host w
  · exact h.2.2.2.2.1 w hs hw
  · exact h.2.2.2.1 w hs

end GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

end
