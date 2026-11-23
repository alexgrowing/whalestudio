import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResiduesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityLatticeCountRelationStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.ModelCount

theorem telescope (S S₀ m : ℤ → ℕ) (h : ∀ y, S y + m (y + 1) = S₀ y + m y) (a : ℤ) (L : ℕ) :
    ∑ j ∈ Finset.range L, S (a + j) + m (a + L) = ∑ j ∈ Finset.range L, S₀ (a + j) + m a := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step := h (a + L)
    have e : a + ((L + 1 : ℕ) : ℤ) = a + L + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e]
    omega

theorem eq_of_cast_eq {k : Type} [Field k] (l : ℕ) [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ y - u := ((CharP.intCast_eq_intCast k l).mp h).dvd
  have hz : y - u = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem sum_resCount {k : Type} [Field k] (U : Multiset ℤ) (w a : ℤ) (L : ℕ) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ u ∈ U, (p u → a ≤ u ∧ u < a + L) ∧
      ∀ y : ℤ, a ≤ y → y < a + L → (u : k) = (y : k) → u = y ∧ p u) :
    ∑ j ∈ Finset.range L, resCount U w ((a + j - w : ℤ) : k) = Multiset.card (U.filter p) := by
  classical
  induction U using Multiset.induction_on with
  | empty => simp [resCount]
  | cons u U ih =>
    have hU := ih (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    have hu := h u (Multiset.mem_cons_self u U)
    have split : ∀ x : k, resCount (u ::ₘ U) w x =
        (if ((u - w : ℤ) : k) = x then 1 else 0) + resCount U w x := by
      intro x
      unfold resCount
      rw [Multiset.filter_cons, Multiset.card_add]
      split_ifs <;> simp
    simp only [split]
    rw [Finset.sum_add_distrib, hU, Multiset.filter_cons, Multiset.card_add]
    congr 1
    have tr : ∀ j : ℕ, (((u - w : ℤ) : k) = ((a + j - w : ℤ) : k)) ↔ ((u : k) = ((a + j : ℤ) : k)) := by
      intro j
      push_cast
      exact sub_left_inj
    by_cases hp : p u
    · rw [if_pos hp, Multiset.card_singleton]
      obtain ⟨ha, hb⟩ := hu.1 hp
      rw [Finset.sum_eq_single (u - a).toNat]
      · rw [if_pos]
        rw [tr]
        congr 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        have := (hu.2 (a + j) (by omega) (by have := Finset.mem_range.mp ‹j ∈ Finset.range L›; omega) ((tr j).mp hc)).1
        omega
      · intro hn
        exfalso
        exact hn (Finset.mem_range.mpr (by omega))
    · rw [if_neg hp, Multiset.card_zero]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hc
      have hj' := Finset.mem_range.mp hj
      exact hp (hu.2 (a + j) (by omega) (by omega) ((tr j).mp hc)).2

theorem exists_of_resCount_ne {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k} (h : resCount U w x ≠ 0) :
    ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero h)
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 N hN hle i
  have hNabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T N hN).2
  have hSabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model).2
  have hs : Dt.sg l i = GlobalTheory.PhiGam.sg l Dt.h i := rfl
  have hsh := GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D M.T) Dt.h Dt.w N M.Nstd hNabc.1 hSabc.1 hNabc.2.1 hSabc.2.1 i
  rw [← hs] at hsh
  have hP : N i ≤ sh (-(Dt.sg l i : ℤ)) (M.Nstd i) := by
    have h' := sh_le_sh (-(Dt.sg l i : ℤ)) hsh
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  have tel := fun y : ℤ => GlobalTheory.T.senMultiplicity_lattice_count_relation R ((F.D M.T).γ i) ((F.D M.T).γ_semi i) (N i) (M.Nstd i)
    (hNabc.1 i) (hSabc.1 i) (hle i) (hNabc.2.2 i) (hSabc.2.2 i) (Dt.sg l i) hP (y : k)
  have rel : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((y + 1 : ℤ) : k) =
      sen ((F.D M.T).γ i) (M.Nstd i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) := by
    intro y
    rw [Int.cast_add, Int.cast_one]
    exact (tel y).1
  have mz : ∀ y : ℤ, qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ Dt.sg l i ∧ ∃ u ∈ Dt.U i, (u : k) = ((y - j + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨j, hj1, hj2, hj⟩ := (tel y).2 hy
    rw [M.std_sen] at hj
    obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne hj
    refine ⟨j, hj1, hj2, u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  have sz : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) ≠ 0 → ∃ u ∈ Dt.U i, (u : k) = ((y + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 M.T M.T LinearMap.id LinearMap.id N (fun _ _ => rfl)
      (fun _ _ hab => hab) (fun _ _ => rfl) (fun b => ⟨b, rfl⟩) hN i (y : k) hy
    refine ⟨u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  obtain ⟨-, hwin, hG, hB⟩ := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i
  have hT1 := h1 i
  have ht := Dt.one_le_letterBlockLength
  have e1 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((0 : ℤ) : k) = 0 := by
    by_contra hne
    obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz 0 hne
    exact hwin u hu _ (by omega) (by omega) hux
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_contra hne
    obtain ⟨u, hu, hux⟩ := sz a (by simpa using hne)
    exact hwin u hu _ (by omega) (by omega) hux
  · intro hG'
    obtain ⟨hGU, hGc, hw1, hwt⟩ := hG hG'
    have hL : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel (-Dt.w i) (Dt.w i).toNat
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i + ((Dt.w i).toNat : ℤ) : ℤ) : k) = 0 := by
      rw [hL, neg_add_cancel]
      exact e1
    have e2 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz (-Dt.w i) hne
      exact hGU u hu _ (by omega) (by omega) hux
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) 0 (Dt.w i).toNat (· < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by omega⟩, fun y hy0 hyL hc => ?_⟩
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowG i hG' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · exact absurd hc (hGc u hcl y hy0 (by omega)))
    have e3 : ∀ j : ℕ, ((0 : ℤ) + (j : ℤ) - Dt.w i) = -Dt.w i + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (M.Nstd i) ((-Dt.w i + j : ℤ) : k) = Dt.d i := by
      change _ = Multiset.card ((Dt.U i).filter (· < Dt.w i))
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [e0, e2, hsum'] at tl
    omega
  · intro hB'
    obtain ⟨hBU, hBc, htw, hwη⟩ := hB hB'
    have hwst : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    have hL : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel 0 ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i)
        (((0 : ℤ) + (((Dt.wst i).toNat + 1 + (Dt.sg l i + 1) : ℕ) : ℤ) : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [e0, e1, Finset.sum_range_add] at tl
    have hz : ∑ j ∈ Finset.range (Dt.sg l i + 1),
        sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + (((Dt.wst i).toNat + 1 + j : ℕ) : ℤ) : ℤ) : k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      obtain ⟨u, hu, hux⟩ := sz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [hz] at tl
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) (Dt.w i) ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
      (fun u => ¬ u < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by push_cast; omega⟩, fun y hy0 hyL hc => ?_⟩
      push_cast at hyL
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowBd i hB' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · by_cases hyh : y ≤ (Dt.h i : ℤ)
        · exact absurd hc (hBc u hcl y (by omega) hyh)
        · exact absurd hc (hBU u (Multiset.mem_add.mpr (Or.inr hcl)) y (by omega) (by omega)))
    have e3 : ∀ j : ℕ, (Dt.w i + (j : ℤ) - Dt.w i) = 0 + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1)),
        sen ((F.D M.T).γ i) (M.Nstd i) (((0 : ℤ) + j : ℤ) : k) = Multiset.card ((Dt.U i).filter (fun u => ¬ u < Dt.w i)) := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [hsum'] at tl
    have hfirst : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + j : ℤ) : k) =
        ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
    have hsplit := congrArg Multiset.card (Multiset.filter_add_not (· < Dt.w i) (Dt.U i))
    rw [Multiset.card_add] at hsplit
    have hU : Multiset.card (Dt.U i) = r := Dt.card_eq i
    have hd : Dt.d i = Multiset.card ((Dt.U i).filter (· < Dt.w i)) := rfl
    rw [hfirst] at tl
    omega

end GlobalTheory.ModelCount
