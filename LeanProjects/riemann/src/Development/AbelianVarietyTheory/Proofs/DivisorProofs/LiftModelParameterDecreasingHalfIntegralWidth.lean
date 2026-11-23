import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ParWidth

theorem mem_holPar_kapW {Rk : Ranks} (h : HCParam Rk) (p q : ℕ) (hpq : Odd (p + q)) {x : ℚ} {b : Bool}
    (hx : (x, b) ∈ Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    ∃ n < p + q, x = Formalism.L2.NTheta.lamAt h n := by
  unfold Formalism.L2.NTheta.holPar at hx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
  have e := Formalism.L2.NTheta.holEnt_kapW h p q hpq a
  have hx' : x = Formalism.L2.NTheta.holEnt p q (Formalism.L2.NTheta.kapW h p q) a := (congrArg Prod.fst ha).symm
  rcases a with i | c
  · exact ⟨i, by omega, hx'.trans (by simpa using e)⟩
  · exact ⟨p + c, by omega, hx'.trans (by simpa using e)⟩

theorem lamAt_anti {Rk : Ranks} (h : HCParam Rk) {n n' : ℕ} (hnn : n ≤ n') (hn : n' < Rk.r) :
    Formalism.L2.NTheta.lamAt h n' ≤ Formalism.L2.NTheta.lamAt h n := by
  have mono : ∀ d : ℕ, n + d < Rk.r → Formalism.L2.NTheta.lamAt h (n + d) ≤ Formalism.L2.NTheta.lamAt h n := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (n + d) (by omega)).le.trans (ih (by omega))
  have := mono (n' - n) (by omega)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lamAt_b {Rk : Ranks} (h : HCParam Rk) (c : ℕ) (hc : c < Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp

theorem le_toNat_floor (x : ℚ) : x ≤ ((⌊x⌋.toNat : ℕ) : ℚ) + 1 := by
  have h1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℚ) ≤ (((⌊x⌋.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
  rw [Int.cast_natCast] at h2
  linarith

end GlobalTheory.LowRow.ParWidth

namespace GlobalTheory.LowRow.ParWidth

theorem width_le (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) 0 - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) (D.R.r - 1) ≤
      (degAt D i σ ρ : ℚ) + D.R.nV + 1 := by
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hp : pW D i ρ = D.R.k + i := by simp only [pW, hsig, Ranks.sigW]; omega
  have hq : qW D i ρ = D.R.m - (i + 1) := by simp only [qW, hsig, Ranks.sigW]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  set h := D.hc (lab σ ρ) with hh
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hnV : (D.R.nV : ℚ) = (D.R.k : ℚ) + D.R.m - 1 + D.R.t := by
    simp only [Ranks.nV, Ranks.r]; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring

  have hP0 : (aPlAt D i σ ρ 0 : ℚ) + 1 ≥
      Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - (0 + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    have := le_toNat_floor (Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - ((0 : ℕ) + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2)
    unfold aPlAt aPl
    rw [hp, if_pos (by omega)]
    simpa using this
  have hdeg : (aPlAt D i σ ρ 0 : ℚ) + (if 0 < qW D i ρ then (aMiAt D i σ ρ 0 : ℚ) else 0) ≤ degAt D i σ ρ := by
    have e1 : aPlAt D i σ ρ 0 ≤ ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n :=
      Finset.single_le_sum (f := aPlAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have e2 : (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) ≤ ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n := by
      split_ifs with hq0
      · exact Finset.single_le_sum (f := aMiAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hq0)
      · exact Nat.zero_le _
    have e3 := Nat.add_le_add e1 e2
    unfold degAt
    have : ((aPlAt D i σ ρ 0 + (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) : ℕ) : ℚ) ≤
        ((∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n : ℕ) : ℚ) := by
      exact_mod_cast e3
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  by_cases hq0 : (i : ℕ) + 1 < D.R.m
  · have hqpos : 0 < qW D i ρ := by rw [hq]; omega
    rw [if_pos hqpos] at hdeg
    have hM0 : (aMiAt D i σ ρ 0 : ℚ) + 1 ≥
        -(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
      have := le_toNat_floor (-(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2))
      unfold aMiAt aMi
      rw [hp, hq, if_pos (by omega), show D.R.k + ↑i + (D.R.m - (↑i + 1) - 0) - 1 = D.R.r - 1 by omega]
      simpa using this
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    have c2 : (((D.R.m - (i + 1) : ℕ) : ℚ)) = D.R.m - (i : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1] at hP0
    rw [c2] at hM0
    rw [hnV]
    linarith
  · have him : (i : ℕ) = D.R.m - 1 := by omega
    rw [if_neg (by rw [hq]; omega), add_zero] at hdeg
    have hb : Formalism.L2.NTheta.lamAt h (D.R.r - 1) = -h.b i := by
      rw [show D.R.r - 1 = D.R.k - 1 + (i : ℕ) by omega, lamAt_b h i i.2]
    have hg := h.gap_be i
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    rw [c1] at hP0
    have hmi : (i : ℚ) = D.R.m - 1 := by
      rw [him, Nat.cast_sub (by omega)]; simp
    rw [hnV, hb]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith

end GlobalTheory.LowRow.ParWidth

open GlobalTheory.LowRow.ParWidth in

theorem GlobalTheory.LowRow.lam_par_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hC i σ s hσ ρ
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hσ.2
  have hat : labE σ (lab σ ρ) = tauE D ρ := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  obtain ⟨hanti, qv, hqv, hS⟩ := (R.MW i σ).enum ρ
  have hpar : parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) := if_pos hat
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hr : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    rw [hsig]; simp only [Ranks.sigW, Ranks.r]; omega
  have hrodd : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hodd : Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := hr ▸ hrodd
  have hent : ∀ a, ∃ n < D.R.r, (R.MW i σ).lam ρ a = ((Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n : ℚ) : ℝ) := by
    intro a
    have hmem : (qv a, (R.MW i σ).ε ρ a) ∈ parAt (Wc D i) σ ρ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hpar] at hmem
    obtain ⟨n, hn, e⟩ := mem_holPar_kapW _ _ _ hodd hmem
    exact ⟨n, hr ▸ hn, by rw [hqv a, e]⟩
  have hrank : (Wc D i).rank = D.R.r := by
    rw [← hr]; exact (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).symm
  refine ⟨hanti, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨n, -, e⟩ := hent a
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) n
    obtain ⟨w, hw⟩ := hrodd
    refine ⟨z - w, ?_⟩
    rw [e, hz, hrank, hw]
    push_cast
    ring
  · obtain ⟨n, hn, ea⟩ := hent a
    obtain ⟨n', hn', eb⟩ := hent b
    have hW := width_le D i σ ρ
    have l1 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n) hn
    have l2 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n') hn'
    have u1 := lamAt_anti (D.hc (lab σ ρ)) (show n ≤ D.R.r - 1 by omega) (by omega)
    have u2 := lamAt_anti (D.hc (lab σ ρ)) (show n' ≤ D.R.r - 1 by omega) (by omega)
    have key : |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n'| ≤
        (degAt D i σ ρ : ℚ) + D.R.nV + 3 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [ea, eb, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast key
