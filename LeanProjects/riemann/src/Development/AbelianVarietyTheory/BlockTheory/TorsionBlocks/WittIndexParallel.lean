import Mathlib
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

def nu (m j : ℕ) : ℕ := if j < m then ⌈((m : ℚ) - 1 - j) / 2⌉₊ else 0

def OddRankWitt (D : D7) : Prop :=
  ∀ (V : HSp D) (p q : ℕ), Odd V.rank → p + q = V.rank → q < p → ParallelSig V p q →
    Formalism.MainNotions.KudlaSiegelWeil.WittIdx V q

def RowSpaceWitt (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → Formalism.MainNotions.KudlaSiegelWeil.WittIdx (D.sp.W j : HSp D) (D.R.m - j)

def ChainWitt (D : D7) : Prop :=
  ∀ t : ℕ, Odd t → D.R.r + 5 ≤ t → ∀ j : ℕ, j ≤ D.R.m →
    ∀ (Y : HSp D) (p : ℕ), Y.rank = D.R.r + j * t → p + nu D.R.m j = D.R.r + j * t →
      ParallelSig Y p (nu D.R.m j) →
        Formalism.MainNotions.KudlaSiegelWeil.WittIdx Y (nu D.R.m j) ∧
        ((nu D.R.m j : ℚ) ≤ (D.R.m : ℚ) / 2 ∧ (D.R.m : ℚ) / 2 < (t : ℚ) / 2) ∧
        (1 ≤ j → (nu D.R.m j : ℚ) ≤ (D.R.m : ℚ) / 2 - 1)

def WittIndexStatement : Prop :=
  ∀ D : D7, OddRankWitt D ∧ RowSpaceWitt D ∧ ChainWitt D

theorem nu_eq (m j : ℕ) : nu m j = (m - j) / 2 := by
  unfold nu
  split_ifs with h
  · obtain ⟨c, rfl⟩ : ∃ c, m = j + c + 1 := ⟨m - j - 1, by omega⟩
    have e : (((j + c + 1 : ℕ) : ℚ) - 1 - j) / 2 = (c : ℚ) / 2 := by push_cast; ring
    rw [e]
    apply le_antisymm
    · rw [Nat.ceil_le, div_le_iff₀ (by norm_num)]
      have : c ≤ (j + c + 1 - j) / 2 * 2 := by omega
      exact_mod_cast this
    · by_contra hlt
      have h1 : (c : ℚ) / 2 ≤ (⌈(c : ℚ) / 2⌉₊ : ℚ) := Nat.le_ceil _
      rw [div_le_iff₀ (by norm_num)] at h1
      have h2 : c ≤ ⌈(c : ℚ) / 2⌉₊ * 2 := by exact_mod_cast h1
      omega
  · omega

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

example (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Odd (D.sp.W j).rank ∧ (D.R.k + j - 1) + (D.R.m - j) = (D.sp.W j).rank ∧ D.R.m - j < D.R.k + j - 1 ∧
      ParallelSig (D.sp.W j : HSp D) (D.R.k + j - 1) (D.R.m - j) := by
  have hr := D.sp.W_rank j h1 h2
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  unfold Ranks.r at hr
  refine ⟨⟨a + b - 1, by omega⟩, by omega, by omega,
    parallelSig_of_sigOK (D.sp.W_sig j) (D.sp.W_sigval j h1 h2)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
