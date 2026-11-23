import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace FrameShapeLemmas

theorem shape_even (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf lam (Fin.cast hm.symm t) = (ν (t.val + 1)).toNat - (ν n).toNat := by
  subst hm
  have h1 := hlam t
  have h2 := hlam (Fin.last m₀)
  have h3 : lam (Fin.last m₀) ≤ lam t := hanti (Fin.le_last t)
  have h4 := hnn (t.val + 1)
  have h5 := hnn (m₀ + 1)
  rw [Fin.val_last] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  omega

theorem shape_odd (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf (fun i => -lam i.rev) (Fin.cast hm.symm t) = (ν 1).toNat - (ν (t.rev.val + 1)).toNat := by
  subst hm
  have h1 := hlam t.rev
  have h2 := hlam 0
  have h3 : lam t.rev ≤ lam 0 := hanti (Fin.zero_le _)
  have h4 := hnn (t.rev.val + 1)
  have h5 := hnn 1
  rw [Fin.val_zero, zero_add] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  beta_reduce
  rw [Fin.rev_last]
  omega

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem hlamS (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (l : ℕ) (hl : j + 1 ≤ l + 1) (i : Fin (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1)) :
    X.nuv v (l + 1) s (i.val + 1) =
      liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) i + X.Fl.w v (l + 1) s := by
  unfold liftWt
  split_ifs with h
  · exact nuv_low X l v s i.val h
  · refine nuv_high X l v s i.val h ?_
    have := i.isLt
    have h2 : (j + 1) * (X.Fl.t + 1) ≤ (l + 1) * (X.Fl.t + 1) := Nat.mul_le_mul_right _ hl
    unfold NN
    show i.val + 1 ≤ X.G.P.m + 1 + (l + 1) * (X.Fl.t + 1)
    omega

theorem not_even_of_odd {n' : ℕ} {s : Fin n'} (h : IsOddPos s) : ¬ Even s.val := by
  rw [Nat.not_even_iff]; exact h

theorem even_of_not_odd {n' : ℕ} {s : Fin n'} (h : ¬ IsOddPos s) : Even s.val :=
  Nat.even_iff.2 (by unfold IsOddPos at h; omega)

theorem c1 (j : ℕ) (b : BX X) : nuM X j b = nuS X j b := by
  funext t
  unfold nuS muX cX eX
  cases j with
  | zero =>
    show nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact shape_odd _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact absurd (even_of_not_odd h2) h1
  | succ j =>
    show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact absurd (even_of_not_odd h2) h1

theorem nuv_top (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.nuv v (j + 1) s (NN X.G.P.m X.t (j + 1)) = 0 := by
  apply nuv_zero X v j s
  unfold NN
  have : j * (X.t + 1) < (j + 1) * (X.t + 1) := by nlinarith
  omega

theorem c2 (j : ℕ) (b : BX X) : nuM X (j + 1) b = nuT X j b := by
  funext t
  unfold nuT muX cX
  show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
  unfold lamAt
  split_ifs with h1 h2 h2
  · exact absurd h1 (not_even_of_odd h2)
  · have := shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
    rw [nuv_top X j b.1 b.2] at this
    refine this.trans ?_
    simp
  · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
  · exact absurd (even_of_not_odd h2) h1

theorem nuv_anti (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) {a c : ℕ} (h : a ≤ c) :
    X.nuv v (j + 1) s (c + 1) ≤ X.nuv v (j + 1) s (a + 1) := by
  by_cases hc : c < X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1
  · rw [hlamS X j v s j le_rfl ⟨c, hc⟩, hlamS X j v s j le_rfl ⟨a, lt_of_le_of_lt h hc⟩]
    have := X.Fl.domJ (j + 1) v s (show (⟨a, lt_of_le_of_lt h hc⟩ : Fin _) ≤ ⟨c, hc⟩ from h)
    linarith
  · rw [nuv_zero X v j s (c + 1) (by
      have h1 : NN X.G.P.m X.t j ≤ NN X.G.P.m X.t (j + 1) := NN_le X j
      have h2 : NN X.G.P.m X.t (j + 1) = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1) := rfl
      omega)]
    exact nuv_nonneg X v j s _

theorem c3 (j n : ℕ) (b : BX X) : Antitone (muX X j n b) := by
  intro a c hac
  unfold muX
  exact Int.toNat_le_toNat (nuv_anti X j b.1 b.2 hac)

theorem c4 (j n : ℕ) (b : BX X) (t : Fin n) : muX X j n b t ≤ cX X j b := by
  unfold muX cX
  exact Int.toNat_le_toNat (nuv_le_first X b.1 j b.2 _)

theorem c56 (j n : ℕ) (h1 : NN X.G.P.m X.t j ≤ n) (h2 : n ≤ NN X.G.P.m X.t (j + 1)) (b : BX X) (k : ℕ) :
    colH (muX X j n b) k = X.colHt b.1 (j + 1) b.2 k := by
  unfold colH muX Sys.colHt
  rw [BidetPairing.card_fin_filter n fun t => k < (X.nuv b.1 (j + 1) b.2 (t + 1)).toNat]
  refine Finset.card_bij (fun t _ => t + 1) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Int.lt_toNat.1 ht.2⟩
  · intro a _ c _ h
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    have hin : i ≤ n := by
      by_contra hc
      have := nuv_zero X b.1 j b.2 i (by omega)
      rw [this] at hi
      have := hi.2
      omega
    refine ⟨i - 1, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show i - 1 + 1 = i by omega]
    exact Int.lt_toNat.2 hi.2

theorem NJ_pos (j : ℕ) : 0 < NN X.G.P.m X.t j := by unfold NN; omega

theorem c7 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) : eX X j b ≤ muX X j (NJ X j) b t := by
  unfold eX muX
  have h := nuv_anti X j b.1 b.2 (show t.val ≤ NJ X j - 1 by have := t.isLt; omega)
  have hN : NJ X j - 1 + 1 = NJ X j := Nat.sub_add_cancel (NJ_pos X j)
  rw [hN] at h
  exact Int.toNat_le_toNat h

theorem c8 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) (ht : t.val + 1 = NJ X j) : muX X j (NJ X j) b t = eX X j b := by
  unfold eX muX
  rw [ht]

theorem eJ_odd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (h : IsOddPos s) : eJ X j v s = -X.G.P.lam0 v s 0 := by
  have h1 := numO X j v s h
  have h2 : cMu X j v s = X.G.P.lam0 v s ⟨0, by omega⟩ + X.Fl.w v (j + 1) s := nuv_low X j v s 0 (by omega)
  have h3 : X.w v (j + 1) s = X.Fl.w v (j + 1) s := rfl
  have h4 : (⟨0, by omega⟩ : Fin (X.G.P.m + 1)) = 0 := rfl
  rw [h4] at h2
  linarith

theorem c9 (j : ℕ) (b : BX X) (h : ¬ IsOddPos b.2) :
    (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2 := by
  obtain ⟨h1, h2⟩ := numE X j b.1 b.2 h
  refine ⟨?_, ?_⟩
  · unfold eX
    rw [Int.toNat_of_nonneg h1, h2]
  · have h3 := hlamS X j b.1 b.2 j le_rfl (Fin.last _)
    have h4 : X.nuv b.1 (j + 1) b.2 ((Fin.last (X.G.P.m + (j + 1) * (X.Fl.t + 1))).val + 1) = 0 := by
      have := nuv_top X j b.1 b.2
      rw [Fin.val_last]
      have e : X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1 = NN X.G.P.m X.t (j + 1) := by
        show _ = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1)
        omega
      rw [e]; exact this
    rw [h4] at h3
    have h5 : eJ X (j + 1) b.1 b.2 =
        liftWt X.Fl.t X.G.P.m (X.G.P.lam0 b.1 b.2) (fun i => X.Fl.w b.1 i b.2) (j + 1) (Fin.last _) := by
      show lamAt _ b.2 _ = _
      unfold lamAt
      rw [if_pos (even_of_not_odd h)]
      rfl
    rw [h5]
    have h6 : X.w b.1 (j + 1) b.2 = X.Fl.w b.1 (j + 1) b.2 := rfl
    linarith

theorem c10 (j : ℕ) (b : BX X) (h : IsOddPos b.2) :
    (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2 := by
  refine ⟨?_, by rw [eJ_odd X (j + 1) b.1 b.2 h, eJ_odd X j b.1 b.2 h]⟩
  have h1 := numO X j b.1 b.2 h
  rw [← h1]
  exact cMu_toNat X b.1 j b.2

end FrameShapeLemmas

open FrameShapeLemmas in
theorem frame_shape_identity_holds : XShape := by
  intro p _ X j b
  exact ⟨c1 X j b, c2 X j b, fun n => c3 X j n b, fun n t => c4 X j n b t, c56 X j _ le_rfl (NN_le X j) b,
    c56 X j _ (NN_le X j) le_rfl b, c7 X j b, c8 X j b, c9 X j b, c10 X j b⟩

end Formalism.L2.PairingIndexBounds.Ent
