import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpaceOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGridModel

variable {D : D7}

def IsSum (A B : LSp D) (c : ℕ) (ε : D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  ∃ d : HermitianOrthogonalExtensionData A.sp B.sp c ε, B.lat = d.lat A.lat 𝔟

theorem exists_sum (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ) (neg : Bool)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h0 : ∀ p, 𝔟 p ≠ 0)
    (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) {ν' q' : ℕ} (h1 : ν + c = ν')
    (h2 : q + (if neg then (c + 1) / 2 else c / 2) = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (if neg then -1 else 1) 𝔟 := by
  obtain ⟨B, ⟨d⟩, hB, hs⟩ := GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature D X.sp (ν - q) q c neg hX.sigOK hX.sig
  refine ⟨⟨B, d.lat X.lat 𝔟⟩, ⟨?_, hB, fun τ => ?_, ?_⟩, d, rfl⟩
  · have := d.rank
    rw [hX.rank] at this
    exact this.symm.trans h1
  · rw [hs τ]
    cases neg <;> simp only [Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h2 ⊢ <;> omega
  · exact GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D X.sp B c _ d X.lat 𝔟 (by cases neg <;> simp) hX.sd h0 hd

theorem exists_line (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) :
    ∃ Y : LSp D, Y.IsV (ν + 1) q ∧ IsSum X Y 1 1 fun _ => 1 := by
  refine exists_sum X hX hq 1 false (fun _ => 1) (fun _ => one_ne_zero) (fun _ x => ?_) rfl rfl
  rw [inv_one, FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff]
  have key : ∀ y : D.host.E, (∃ a : 𝓞 D.host.E, algebraMap _ _ a = y) → ∃ a : 𝓞 D.host.E, algebraMap _ _ a = star y := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, Examples₂.star_isIntegral _ a.2⟩, rfl⟩
  exact ⟨key x, fun h => by simpa using key _ h⟩

theorem exists_stair (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ)
    {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h0 : 𝔞 ≠ 0) (hc : ∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) {ν' q' : ℕ}
    (h1 : ν + c = ν') (h2 : q + (c + 1) / 2 = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (-1) (stairId 𝔞 𝔞' c) :=
  exists_sum X hX hq c true _ (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).1)
    (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).2) h1 h2

theorem nonempty_vertices : ∀ (D : D7) (T : Type) (L : LevCh D T) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
    IsSelfDualC (Yc D 0) (L.ΛY 0) → 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → Nonempty (Vertices L 𝔞 𝔞') := by
  intro D T L 𝔞 𝔞' hY h0 hc
  classical
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  obtain ⟨μ, hμ⟩ := D.R.m_even
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = (D.R.r + 5) + 1 := rfl
  have hVr : ∀ i j, D.R.m ≤ rankV D i j := fun i j => by unfold rankV; omega
  have hPr : ∀ i, D.R.m ≤ rankP D i := fun i => by unfold rankP nRk; omega
  obtain ⟨hA0, hAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1

  have hstd : ∀ ν q : ℕ, ∃ X : LSp D, q ≤ ν → X.IsV ν q := fun ν q => by
    by_cases h : q ≤ ν
    · exact (GlobalTheory.ChiGrid.exists_isV D ν q h).imp fun _ hX _ => hX
    · exact ⟨⟨Yc D 0, L.ΛY 0⟩, fun h' => absurd h' h⟩
  choose S hS using hstd

  have hY0 : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV D.R.r (D.R.m / 2) := by
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, hY⟩
    · exact (D.sp.Y_rank 0 (Nat.zero_le _)).trans (by simp [Ranks.rankY])
    · refine (D.sp.baseSpace_signature_eq τ).trans ?_
      simp only [Ranks.sigY0, Ranks.rS, Prod.mk.injEq]
      omega
  obtain ⟨P₀, hP₀, d0, hd0⟩ := exists_line _ hY0 (by omega)
  let P : ℕ → LSp D := xOf P₀ fun i => S (rankP D i) ((D.R.m - i + 1) / 2)
  have hP : ∀ i, i ≤ D.R.m → (P i).IsV (rankP D i) ((D.R.m - i + 1) / 2) := by
    rintro (_ | i) hi
    · have e1 : rankP D 0 = D.R.r + 1 := by simp [rankP, nRk]
      have e2 : (D.R.m - 0 + 1) / 2 = D.R.m / 2 := by omega
      rw [e1, e2]; exact hP₀
    · exact hS _ _ (by have := hPr (i + 1); omega)

  have hVm : (S (rankV D D.R.m D.R.m) 0).IsV (rankV D D.R.m D.R.m) 0 := hS _ _ (Nat.zero_le _)
  obtain ⟨Xm, hXm, htop⟩ := exists_line _ hVm (Nat.zero_le _)
  let Xs : ℕ → LSp D := fun j => if j = D.R.m then Xm else S (rankX D j) 0
  have hX : ∀ j, (Xs j).IsV (rankX D j) 0 := fun j => by
    by_cases h : j = D.R.m
    · have e1 : rankX D j = rankV D D.R.m D.R.m + 1 := by
        simp only [h, rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
      simp only [Xs, if_pos h]
      rw [e1]; exact hXm
    · simp only [Xs, if_neg h]
      exact hS _ _ (Nat.zero_le _)

  have hcol : ∀ i, ∃ Y : LSp D, 1 ≤ i → i ≤ D.R.m →
      Y.IsV (rankV D i 0) ((D.R.m - 0) / 2) ∧ IsSum (P i) Y (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := fun i => by
    by_cases h : 1 ≤ i ∧ i ≤ D.R.m
    · refine (exists_stair (P i) (hP i h.2) (by have := hPr i; omega) (i - 1) h0 hc ?_ (by omega)).imp fun _ hZ _ _ => hZ
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
    · exact ⟨P₀, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose C hC using hcol

  have hrow : ∀ j, ∃ Y : LSp D, j < D.R.m →
      Y.IsV (rankV D D.R.m j) ((D.R.m - j) / 2) ∧
        IsSum (Xs j) Y (D.R.m - 1 - j) (-1) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := fun j => by
    by_cases h : j < D.R.m
    · refine (exists_stair (Xs j) (hX j) (Nat.zero_le _) (D.R.m - 1 - j) hA0 hAc ?_ (by omega)).imp fun _ hZ _ => hZ
      simp only [rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel, mul_add, mul_one]; omega
    · exact ⟨P₀, fun h1 => absurd h1 h⟩
  choose R hR using hrow
  let Vs : ℕ → ℕ → LSp D := fun i j =>
    if j = 0 then C i else if i = D.R.m ∧ j < D.R.m then R j else S (rankV D i j) ((D.R.m - j) / 2)
  have hv : ∀ i j, 1 ≤ i → vtxOf L Vs i j = Vs i j := by
    rintro (_ | i) j hi
    · omega
    · rfl
  have hx : ∀ X₀ j, 1 ≤ j → xOf X₀ Xs j = Xs j := by
    rintro X₀ (_ | j) hj
    · omega
    · rfl
  have hV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → (Vs i j).IsV (rankV D i j) ((D.R.m - j) / 2) := by
    intro i j h1 h2 h3
    simp only [Vs]
    split_ifs with ha hb
    · subst ha; exact (hC i h1 h2).1
    · rw [hb.1]; exact (hR j hb.2).1
    · exact hS _ _ (by have := hVr i j; omega)
  have h1 : ∀ i, 1 ≤ i → i ≤ D.R.m → IsSum (P i) (vtxOf L Vs i 0) (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := by
    intro i h h'
    rw [hv i 0 h]
    exact (hC i h h').2
  have h2 : ∀ j, j + 1 < D.R.m → IsSum (Xs (j + 1)) (vtxOf L Vs D.R.m (j + 1)) (D.R.m - 1 - (j + 1)) (-1)
      (stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) := by
    intro j h
    have e : Vs D.R.m (j + 1) = R (j + 1) := by
      simp only [Vs]
      rw [if_neg (Nat.succ_ne_zero j), if_pos ⟨trivial, h⟩]
    rw [hv _ _ (by omega), e]
    exact (hR _ h).2
  have h3 : IsSum (vtxOf L Vs D.R.m D.R.m) (xOf (P D.R.m) Xs D.R.m) 1 1 fun _ => 1 := by
    have e : Vs D.R.m D.R.m = S (rankV D D.R.m D.R.m) 0 := by
      simp only [Vs]
      rw [if_neg (by omega), if_neg (by omega), Nat.sub_self]
    have e' : Xs D.R.m = Xm := if_pos rfl
    rw [hv _ _ (by omega), hx _ _ (by omega), e, e']
    exact htop
  choose d1 hd1 using h1
  choose d2 hd2 using h2
  obtain ⟨d3, hd3⟩ := h3
  exact ⟨⟨Vs, P, Xs, hV, hP, fun j _ _ => hX j, d0, hd0, d1, hd1, d2, hd2, d3, hd3⟩⟩

theorem exists_gridData {T : Type} (L : LevCh D T) (sc : Consts) (P : Places L) (h0 : P.v0 ∉ S1 D)
    (hY : IsSelfDualC (Yc D 0) (L.ΛY 0)) : ∃ G : GridData L sc, G.pl = P := by
  obtain ⟨X⟩ := GlobalTheory.GridChars.nonempty_chars D T L P sc.cGap h0
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  obtain ⟨V⟩ := nonempty_vertices D T L _ _ hY h1 h2
  exact ⟨⟨P, X, V⟩, rfl⟩

theorem nonempty_gridData_iff {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts) :
    Nonempty (GridData L sc) ↔ ∃ P : Places L, P.v0 ∉ S1 D := by
  refine ⟨fun ⟨G⟩ => ⟨G.pl, G.ch.basePlace_not_mem_chiGridBadPlaces⟩, fun ⟨P, h⟩ => ?_⟩
  obtain ⟨G, -⟩ := exists_gridData L sc P h (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL 0 (Nat.zero_le _)).sd
  exact ⟨G⟩

theorem isV_all {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {sc : Consts} (G : GridData L sc) {X : Node}
    (h : X.InRange D.R.m) : (G.node X).IsV (X.rank D) (X.neg D.R.m) := by
  by_cases h0 : ∀ j, X ≠ .grid 0 j
  · exact G.isV h h0
  · push Not at h0
    obtain ⟨j, rfl⟩ := h0
    exact GlobalTheory.ChiGrid.colY_isV D T L μ0 hL j h.2

theorem chiH_ne_one {T : Type} {L : LevCh D T} {P : Places L} {C : ℝ} (X : Chars P C) {i : ℕ} (h : 1 ≤ i)
    (h' : i ≤ D.R.m) : X.chiH i ≠ 1 := fun e =>
  (X.lev0 i h h' _ (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl)))).2 (by rw [e]; intro x _; rfl)

theorem modul_ne_top {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) : P.modul sc ≠ ⊤ := by
  intro e
  have h : (P.w P.v0).asIdeal ∣ P.modul sc :=
    (dvd_pow_self _ (P.depth_pos sc _).ne').trans (Finset.dvd_prod_of_mem _ (P.mem_S0_of_sum_eq.2 (Or.inl rfl)))
  rw [e, Ideal.dvd_iff_le, top_le_iff] at h
  exact (P.w P.v0).isPrime.ne_top h

theorem nonempty_gridData {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts)
    (hg : ∀ k, D.host.g k % LevelStarExponents.condE D = 1) (h1 : D.host.pde % LevelStarExponents.condE D = 1) (h2 : D.host.pde' % LevelStarExponents.condE D = 1)
    (h3 : ∀ k, q0 D ≠ D.host.g k) (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    Nonempty (GridData L sc) :=
  (nonempty_gridData_iff L μ0 hL sc).2 (GlobalTheory.GridPlaces.exists_places D T L μ0 hL hg h1 h2 h3 h4)

theorem exists_levCh_gridData (C : Formalism.L2.Host.CharFrame D) (sc : Consts)
    (hg : ∀ k, D.host.g k % LevelStarExponents.condE D = 1) (h1 : D.host.pde % LevelStarExponents.condE D = 1) (h2 : D.host.pde' % LevelStarExponents.condE D = 1)
    (h3 : ∀ k, q0 D ≠ D.host.g k) : ∃ L : LevCh D Unit, L.C = C ∧ L.Is () ∧ Nonempty (GridData L sc) := by
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit D C
  refine ⟨L, hC, hL, nonempty_gridData L () hL sc hg h1 h2 h3 fun t PP hP => ?_⟩
  exact absurd (by rw [hL.xi_base]; intro x _; rfl) ((hL.Q_ram () PP).2 (Or.inl hP))

theorem isEmpty_gridData {T : Type} (L : LevCh D T) (sc : Consts) (h : q0 D = D.host.g 0) : IsEmpty (GridData L sc) :=
  ⟨fun G => G.ch.basePlace_not_mem_chiGridBadPlaces ((S1_mem_OmF D).2 (Or.inl (h ▸ G.pl.basePlace_over_qZero)))⟩

theorem ratio_st {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) :
    P.stA sc * P.stAbar sc * (P.modul sc : Ideal (𝓞 D.host.E)) * (P.modulBar sc : Ideal (𝓞 D.host.E)) =
      D.host.AA * D.host.AAbar := by
  have h1 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (P.modul_ne_bot sc)
  have h2 : ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun h =>
    ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).1 (by rw [Places.stA, h]; simp)
  unfold Places.stA Places.stAbar
  field_simp

open GlobalTheory.SignedHC in

theorem par_core {T : Type} (C : ℝ) (τ : D.what₂.Tau) {i : ℕ} (h : (Pair.core i : Pair T).InRange D.R.m) :
    Node.par D C (Pair.core i : Pair T).big τ =
      lift (Pair.core i : Pair T).ori (Pair.centre D C (Pair.core i : Pair T) τ) (Pair.len D (Pair.core i : Pair T))
        (Node.par D C (Pair.core i : Pair T).small τ) := by
  change (num D C τ).parPi (i + 1) = liftMinus ((num D C τ).cen ((num D C τ).m - i)) ((num D C τ).s - 1) ((num D C τ).parPi i)
  have hi : i + 1 ≤ (num D C τ).m := h
  have hm := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hs2 : 2 ≤ (num D C τ).s := by change 2 ≤ D.R.r + 6; omega
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  generalize num D C τ = G at *
  have hc := abs_le.1 (hm (G.m - i) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
  rw [G.mid_eq (by omega)] at hc
  have hga : (3 : ℚ) ≤ G.ga := by exact_mod_cast (by omega : 3 ≤ G.ga)
  have hle : ∀ {a b : ℕ}, a ≤ b → G.a b ≤ G.a a := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have up : ∀ l, l < G.m - i → (G.cen (G.m - i) : ℚ) < G.a l := fun l hl => by linarith [a_add_le (G := G) hl, hc.2]
  have dn : ∀ l, G.m - i ≤ l → G.a l < (G.cen (G.m - i) : ℚ) := fun l hl => by linarith [hle hl, hc.1]
  have cl : ∀ x ∈ G.cloudHalf, x < (G.cen (G.m - i) : ℚ) := fun x hx => (cloudHalf_lt hx).trans (dn _ (by omega))
  have bl : ∀ l, G.m - i + 1 ≤ l → l ≤ G.m → ∀ x ∈ G.blockC' l, x < (G.cen (G.m - i) : ℚ) := fun l h1 h2 x hx => by
    linarith [(blockC'_between hm hs hg (by omega) h2 hx).2, a_add_le (G := G) (show G.m - i < l by omega), dn _ le_rfl]
  have sg1 : ∀ l, G.m - i ≤ l → decide (G.m - (i + 1) ≤ l ∨ Even (G.m - (i + 1) - l)) = decide (G.m - i ≤ l ∨ Even (G.m - i - l)) :=
    fun l hl => by rw [decide_eq_true (Or.inl (by omega)), decide_eq_true (Or.inl hl)]
  have sg2 : ∀ l, l < G.m - i → decide (G.m - (i + 1) ≤ l ∨ Even (G.m - (i + 1) - l)) = !decide (G.m - i ≤ l ∨ Even (G.m - i - l)) :=
    fun l hl => by
      rw [← decide_not, decide_eq_decide, Nat.even_iff, Nat.even_iff]; omega
  ext ⟨x, s⟩
  simp only [mem_liftMinus, GlobalTheory.SignedHC.GridData.mem_parPi, Prod.mk.injEq]
  constructor
  · rintro (⟨l, hl, rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨l, h1, h2, hx, rfl⟩)
    · rcases lt_or_ge l (G.m - i) with h' | h'
      · exact Or.inr (Or.inl ⟨up l h', Or.inl ⟨l, hl, rfl, by rw [sg2 l h', Bool.not_not]⟩⟩)
      · exact Or.inl ⟨(dn l h').le, Or.inl ⟨l, hl, rfl, sg1 l h'⟩⟩
    · exact Or.inl ⟨(cl x hx).le, Or.inr (Or.inl ⟨hx, rfl⟩)⟩
    · by_cases e : l = G.m - i
      · exact Or.inr (Or.inr ⟨e ▸ hx, rfl⟩)
      · exact Or.inl ⟨(bl l (by omega) h2 x hx).le, Or.inr (Or.inr ⟨l, by omega, h2, hx, rfl⟩)⟩
  · rintro (⟨h0, ⟨l, hl, rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨l, h1, h2, hx, rfl⟩⟩ | ⟨h0, ⟨l, hl, rfl, hs'⟩ | ⟨hx, -⟩ | ⟨l, h1, h2, hx, -⟩⟩ | ⟨hx, rfl⟩)
    · have : G.m - i ≤ l := by by_contra h'; exact absurd (up l (by omega)) (not_lt.2 h0)
      exact Or.inl ⟨l, hl, rfl, (sg1 l this).symm⟩
    · exact Or.inr (Or.inl ⟨hx, rfl⟩)
    · exact Or.inr (Or.inr ⟨l, by omega, h2, hx, rfl⟩)
    · have : l < G.m - i := by by_contra h'; exact absurd (dn l (by omega)) (not_lt.2 h0.le)
      exact Or.inl ⟨l, hl, rfl, by rw [sg2 l this, ← hs', Bool.not_not]⟩
    · exact absurd (cl x hx) (not_lt.2 h0.le)
    · exact absurd (bl l h1 h2 x hx) (not_lt.2 h0.le)
    · exact Or.inr (Or.inr ⟨G.m - i, by omega, by omega, hx, rfl⟩)

end GlobalTheory.ChiGridModel
