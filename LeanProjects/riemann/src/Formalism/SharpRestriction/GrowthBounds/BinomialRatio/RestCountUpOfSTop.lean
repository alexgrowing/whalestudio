import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem floor_sub_le (x : ℤ) {m : ℝ} (hm : 0 ≤ m) : ⌊(x : ℝ) - m⌋ ≤ x := by
  have h := Int.floor_mono (sub_le_self (x : ℝ) hm)
  rwa [Int.floor_intCast] at h

theorem thr_U [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m) (b : SegBlock s r)
    (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) (i : Fin s)
    (hi : S.sigma ≤ i.val) : ka ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap p S b i.val := by
  have hit : i.val - S.sigma < S.t := by unfold SegData.t; have := i.2; omega
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = i.val - S.sigma :=
    ⟨⟨i.val - S.sigma, by show i.val - S.sigma < S.t + 1; omega⟩, rfl⟩
  have hkt : k.val < S.t := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * i.val + 1
    rw [dif_pos hkt]
    show min (2 * (S.sigma + k.val) + 1) (2 * s + 1) = 2 * i.val + 1
    omega
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b i.val : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dif_pos hkt, WithTop.map_coe]
    have hu : ((uTop S ⟨k.val, hkt⟩ : Fin s) : ℕ) = i.val := by
      show S.sigma + k.val = i.val
      omega
    rw [hu]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

theorem thr_last [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) {m : ℝ} (hm : 0 ≤ m)
    (b : SegBlock s r) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ)
    (hOK : ChainOK (blockData p S aTop aPlus m b).T.J (blockData p S aTop aPlus m b).T.thr ka) :
    ka (Fin.last _) 0 ≤ cap p S b s := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (blockData p S aTop aPlus m b).T.q, k.val = S.t :=
    ⟨⟨S.t, by show S.t < S.t + 1; omega⟩, rfl⟩
  have hkt : ¬ (k.val < S.t) := by omega
  have h := hOK k
  have e1 : finPos (2 * s + 1) ((blockData p S aTop aPlus m b).T.J k) = Fin.last _ := by
    apply Fin.ext
    show min (if h : k.val < S.t then 2 * (uTop S ⟨k.val, h⟩ : ℕ) + 1 else 2 * s + 1) (2 * s + 1) = 2 * s + 1
    rw [dif_neg hkt]
    exact min_self _
  have e3 : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
    show WithTop.map (fun x : ℤ => ⌊(x : ℝ) - m⌋) (if h : k.val < S.t then ((cap p S b (uTop S ⟨k.val, h⟩) : ℤ) : WithTop ℤ)
      else ((cap p S b s : ℤ) : WithTop ℤ)) = _
    rw [dif_neg hkt, WithTop.map_coe]
  rw [e1, e3] at h
  exact (WithTop.coe_le_coe.mp h).trans (floor_sub_le _ hm)

def STopRowsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 i.val ∧
          z.2.2 ⟨2 * i.val + 1, by omega⟩ 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 (i.val + 1)

theorem firstRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hS : STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FirstRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold FirstRowsAt
  intro X _ hD hI hc j m hm rz ry hdig z hz
  have hS' := hS X hD hI hc j m hm rz ry hdig z hz
  obtain ⟨b, ⟨jl, jp⟩, ka⟩ := z
  obtain ⟨⟨hK, -, -⟩, -, -, hok⟩ := hz
  dsimp only at hS' hK hok ⊢
  refine ⟨fun i c hc0 => ?_, fun c hc0 => ?_⟩
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
    · exact hS' i hi
    · have h1 := thr_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok i
        (by omega)
      refine ⟨h1, ?_⟩
      rw [cap_succ]
      have h2 := (hK.2.1 i (by omega)).1
      have h3 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := by
        unfold oEff
        rw [if_neg hi]
      omega
  · have c0 : c = 0 := Fin.ext (by simp [hc0])
    subst c0
    exact thr_last X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) hm b ka hok

def RestSTopRows : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restFirstRows_of (h : RestSTopRows) : RestFirstRows := by
  unfold RestSTopRows TransportedAlt at h
  unfold RestFirstRows TransportedAlt
  intro Cc hCc
  obtain ⟨U0, hU0, h0⟩ := h Cc hCc
  refine ⟨U0, hU0, fun C0 hC0 => ?_⟩
  obtain ⟨U1, hU1, h1⟩ := h0 C0 hC0
  refine ⟨U1, hU1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨U2, hU2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  exact ⟨U2, hU2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => firstRows_of (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

theorem restCountUp_of_STop (hCD : ChainDimAt) (hNB : NumBranchAt) (h : RestSTopRows) : RestCountUp := restCountUp_of_rows hCD hNB (restFirstRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
