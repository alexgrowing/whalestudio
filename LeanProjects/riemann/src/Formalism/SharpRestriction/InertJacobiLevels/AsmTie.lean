import Formalism.SharpRestriction.InertJacobiLevels.SecondTorsionCardPos
import Formalism.SharpRestriction.InertJacobiLevels.AsmErr
import Formalism.SharpRestriction.InertJacobiLevels.AsmKap

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure CoreTie (R : Ranks) (H : Host R) (hc : ↥(R.Psi) → HCParam R) (sc : Scale) (Del : ℝ) (c : ℕ) : Prop where
  hw : 1 ≤ sc.w'' R.n
  c_le : (c : ℝ) ≤ 4 * ((R.k : ℝ) * (4 * Del))
  hcl : (R.k : ℝ) * (4 * Del) + ((R.k : ℝ) - 1) / 2 ≤ c
  hoff : ∀ g : ↥(R.Psi), (g : R.GG) ∉ H.topPlaces → ∀ i : Fin R.k,
    |(((hc g).u i : ℚ) : ℝ) - (((R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c
  hw1 : ∀ g, (c : ℝ) ≤ ej R (hc g) 1 - ((R.k : ℝ) + (2 * ((1 : ℕ) : ℝ) - 1) * ((R.t : ℝ) + 1)) / 2
  g_cls : ∀ i, H.cls (H.g i) = .splitK

def Core.Comparison₂ (X : Core) (sc : Scale) (Del : ℝ) (c : ℕ) : Prop := CoreTie X.1 X.2.1 X.2.2 sc Del c

structure RecMore (D : D7) (gatT : GatTies D) (sc : Scale) where

  mu_tw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ L : SizeData₂ D, L.sc = sc → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L j w = 0

  Aj0 : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0

  S0 : Finset D.what₂.places.Pl

  mu_0 : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ S0

  pos : ∀ (L : SizeData₂ D) (X : G.Inst D L), X.bs = bsA → L.sc = sc → PosHyp gatT X

theorem fval_zero_of_tw {D : D7} {sc : Scale}
    (h : ∀ w, (((D.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D.R.n ∨
      D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ)) → D.what₂.muAt w ≠ D.what₂.mu0)
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w = D.what₂.mu0) (L : SizeData₂ D) (hL : L.sc = sc) (j : ℕ) : Fval L j w = 0 := by
  subst hL
  have h1 : ¬ (((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n ∨
      D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ)) := fun h' => h w h' hw
  rw [not_or] at h1
  refine FvalP_above _ j (not_le.1 h1.1) (fun h' => h1.2 ?_) (fun h' => h1.2 ?_)
  · have h2 : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := h'
    rw [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 <;> simp [h2]
  · simp [h']

end Formalism.MainNotions.Inhab

end
