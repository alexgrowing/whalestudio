import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.Columns.BaseLemmas

namespace GlobalTheory.ColNorms.StepRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem nuW_eq_nu (N : NumDatum) {X : Fields} {Pr : Primes X} (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word)
    (δ : Code N) (h : WeightTie N W pl u δ) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) (l : Fin (N.R.N i)) :
    (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  obtain ⟨h1, h2⟩ := h.2.2 z
  have he : (W.hc u (pl z)).e = (N.hc z).e := congrArg RowPar.e h1
  have hq : N.eQ (i + 1) z = (N.hc z).e ⟨i, hi⟩ := by
    unfold NumDatum.eQ
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  rw [W.nuW_eq u hi, W.lamN_eq u hi.le, he]
  unfold NumDatum.nu NumDatum.srcPar
  rw [hq]
  by_cases hl : l.1 < N.R.k
  · rw [dif_pos hl, dif_pos hl]
    unfold hcToWeightQ rhoVec wG Ranks.N
    rw [h2, Nat.add_sub_cancel]
    push_cast
    ring
  · have hb := N.R.blk_lt hi.le l hl
    rw [dif_neg hl, dif_neg hl, dif_pos hb]
    have hdm := Nat.div_add_mod (l.1 - N.R.k) (N.R.t + 1)
    have hl2 : l.1 = N.R.k + ((N.R.t + 1) * ((l.1 - N.R.k) / (N.R.t + 1)) + (l.1 - N.R.k) % (N.R.t + 1)) := by omega
    have hl3 : ((l.1 : ℕ) : ℚ) = N.R.k + (((N.R.t : ℚ) + 1) * (((l.1 - N.R.k) / (N.R.t + 1) : ℕ) : ℚ) +
        (((l.1 - N.R.k) % (N.R.t + 1) : ℕ) : ℚ)) := by exact_mod_cast hl2
    rw [hl3]
    generalize (N.hc z).e ⟨(l.1 - N.R.k) / (N.R.t + 1), hb⟩ = eb
    generalize (l.1 - N.R.k) / (N.R.t + 1) = B
    generalize (l.1 - N.R.k) % (N.R.t + 1) = r
    unfold wG Ranks.N
    rw [Nat.add_sub_cancel]
    push_cast
    ring

theorem sExp_int (R : Ranks) (z : ℤ) (j : ℕ) :
    (∃ y : ℤ, sExp R (z : ℚ) (j + 1) = y) ∧ ∃ y : ℤ, sExp' R (z : ℚ) (j + 1) = y := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold sExp sExp' Ranks.N
  rw [Nat.add_sub_cancel, ha, hc]
  exact ⟨⟨z - a - j * (c + 1), by push_cast; ring⟩, ⟨z - a - (j + 1) * (c + 1), by push_cast; ring⟩⟩

theorem stepWeights {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau)
    (h0 : ∀ l : Fin (R.N i), 0 ≤ (W.nuW u (i + 1) τ).w l) :
    GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ) := by
  obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨i, hi⟩
  obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩ := sExp_int R z i
  refine ⟨h0, ⟨y', fun l => ?_⟩, ⟨y, fun l => ?_⟩⟩
  · have h := W.nuW_eq_true u hi τ l
    rw [hz, hy'] at h
    exact_mod_cast h
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero
    by_cases hl : l.1 < R.N i
    · rw [dif_pos hl]
      have h := W.nuW_eq_true u hi τ ⟨l.1, hl⟩
      have h' := W.lamTrue_old u hi τ l hl
      rw [hz, hy'] at h
      rw [hz, hy, hy', ← h] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = (((W.nuW u (i + 1) τ).w ⟨l.1, hl⟩ : ℤ) : ℚ) := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2
    · rw [dif_neg hl]
      have h' := W.lamTrue_new u hi τ l hl
      rw [hz, hy] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = 0 := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2

theorem weights_rows : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ)) ∧ ∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp i hi
  obtain ⟨-, hW, -, -, -, -, -, -, hS⟩ := hyp
  refine ⟨fun τ => stepWeights W u hi τ fun l => ?_, fun z l => nuW_eq_nu N W pl u δ hW hi z l⟩
  obtain ⟨z, rfl⟩ := pl.surjective τ
  have h1 := nuW_eq_nu N W pl u δ hW hi z l
  have h2 := (hS.2.2.2.2.1 (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) z l.1 l.2).1
  rw [← h1] at h2
  exact_mod_cast h2

end GlobalTheory.ColNorms.StepRows
