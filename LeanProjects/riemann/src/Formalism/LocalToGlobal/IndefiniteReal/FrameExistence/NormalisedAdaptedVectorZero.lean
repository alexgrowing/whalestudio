import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def betaYOf (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (j : ℕ) : GL (Fin (D.sp.Y j).rank) (EAf D) :=
  if h : j ≤ D.R.m then
    (show GL (Fin (Yc D j).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D) by
      unfold Yc; rw [Nat.min_eq_left h]) ▸ βY j
  else 1

open Classical in

def NormalClauses {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (∀ t : T, NormalFrames (betaYOf βY) e ev z κ s (Pg ∪ Q t ∪ Sd) Pg ∧
      NormalFrame0 (betaYOf βY 0) (Pg ∪ Q t ∪ Sd) Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg

def SDFrames (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  (∀ j, j < D.R.m → IsSDFrame (Yc D j) (βY j) (ΛY j) (D.host.g 0 * D.host.g 1)) ∧
    IsSDFrame D.sp.X' βX ΛX 1 ∧ (∀ i, IsSDFrame (Vc D i) (βV i) (ΛV i) 1) ∧
    ∀ i, IsSDFrame (Wc D i) (βW i) (ΛW i) 1

variable (D) in
open Classical in

def FramesExist {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalClauses Pg Sd Q βY βW

def baseHyperbolicVector (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then ⇑((D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)) else 0

def baseDualHyperbolicVector (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then ⇑((D.sp.Y 0).frame.repr (D.sp.hypF ⟨i, h⟩)) else 0

def baseLineVector : Fin (D.sp.Y 0).rank → D.host.E := ⇑((D.sp.Y 0).frame.repr D.sp.zm)

def kap0 (i : ℕ) : D.host.E := if i = D.R.rS then -(D.sp.T : D.host.E) else 1

def patchE (e : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseHyperbolicVector
  | j + 1 => e (j + 1)

def patchEv (ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseDualHyperbolicVector
  | j + 1 => ev (j + 1)

def patchZ (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E
  | 0 => baseLineVector
  | j + 1 => z (j + 1)

def patchK (κ : ℕ → ℕ → D.host.E) (j i : ℕ) : D.host.E := if j = 0 then kap0 (D := D) i else κ j i

def patchS (s : ℕ → D.host.E) (j : ℕ) : D.host.E := if j = 0 then 1 else s j

def IsHyperbolicFrameAt (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (j : ℕ) :
    Prop :=
  (∀ i < (D.R.m - 1 - j) / 2, ∀ l < (D.R.m - 1 - j) / 2,
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (ev j l)) = (if i = l then 1 else 0) ∧
      (D.sp.Y j).hT (vecY j (e j i)) (vecY j (e j l)) = 0 ∧ (D.sp.Y j).hT (vecY j (ev j i)) (vecY j (ev j l)) = 0) ∧
    ((D.R.m - 1 - j) % 2 = 1 →
      (D.sp.Y j).hT (vecY j (z j)) (vecY j (z j)) = -(D.sp.T : D.host.E) ∧
      ∀ i < (D.R.m - 1 - j) / 2,
        (D.sp.Y j).hT (vecY j (z j)) (vecY j (e j i)) = 0 ∧ (D.sp.Y j).hT (vecY j (z j)) (vecY j (ev j i)) = 0) ∧
    ∀ x : (D.sp.X j).V, ∀ i' < D.R.m - 1 - j,
      (D.sp.Y j).hT (D.sp.iXY j x) (vecY j (adaptedVector e ev z j i')) = 0

theorem is_adapted_vector_system_iff (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) :
    IsAdaptedVectorSystem e ev z ↔ ∀ j < D.R.m, IsHyperbolicFrameAt e ev z j := Iff.rfl

open Classical in

def ColsAt (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E)
    (Pg : Finset (Pl D.host.E)) (PP : Pl D.host.E) (ei : AE D) (j : ℕ) : Prop :=
  (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i →
      ColAt j (βY j).val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) *
          (nfScal κ s j i * adaptedVector e ev z j i r)) ∧
    (∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
      XSpanAt j (βY j).val ei col)

theorem normalFrames_iff (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D))
    (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (S Pg : Finset (Pl D.host.E)) :
    NormalFrames βY e ev z κ s S Pg ↔
      IsAdaptedVectorSystem e ev z ∧ (∀ j i, κ j i ≠ 0) ∧ (∀ j, s j ≠ 0) ∧
      (∀ PP ∈ Pg, ∀ j < D.R.m, ∀ i < D.R.m - 1 - j, PP.valuation D.host.E (nfScal κ s j i) = 1) ∧
      ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ j < D.R.m, ColsAt βY e ev z κ s Pg PP ei j := Iff.rfl

theorem vecY_repr (j : ℕ) (v : (D.sp.Y j).V) : vecY (D := D) j ⇑((D.sp.Y j).frame.repr v) = v := by
  simp [vecY]

theorem vecY_zero (j : ℕ) : vecY (D := D) j 0 = 0 := by
  simp [vecY]

theorem m_sub_one_div_two : (D.R.m - 1 - 0) / 2 = D.R.rS := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  show (D.R.m - 1 - 0) / 2 = D.R.m / 2 - 1
  omega

theorem m_sub_one_mod_two : (D.R.m - 1 - 0) % 2 = 1 := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  omega

theorem adapted_relations_at_zero (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) :
    IsHyperbolicFrameAt (patchE e) (patchEv ev) (patchZ z) 0 := by
  have hd : (D.R.m - 1 - 0) / 2 = D.R.rS := m_sub_one_div_two
  unfold IsHyperbolicFrameAt
  refine ⟨?_, ?_, ?_⟩
  · intro i hi l hl
    rw [hd] at hi hl
    simp only [patchE, patchEv, baseHyperbolicVector, baseDualHyperbolicVector, dif_pos hi, dif_pos hl, vecY_repr]
    refine ⟨?_, D.sp.hyp_ee _ _, D.sp.hyp_ff _ _⟩
    rw [D.sp.hyp_ef]
    simp [Fin.ext_iff]
  · intro _
    refine ⟨?_, ?_⟩
    · simp only [patchZ, baseLineVector, vecY_repr]
      exact D.sp.zm_norm
    · intro i hi
      rw [hd] at hi
      simp only [patchZ, patchE, patchEv, baseLineVector, baseHyperbolicVector, baseDualHyperbolicVector, dif_pos hi, vecY_repr]
      exact D.sp.hyp_orthz ⟨i, hi⟩
  · intro x i _
    unfold adaptedVector
    rw [hd]
    split_ifs with h1 h2
    · simp only [patchE, baseHyperbolicVector, dif_pos h1, vecY_repr]
      exact (D.sp.hyp_orthX _ x).1
    · simp only [patchZ, baseLineVector, vecY_repr]
      exact D.sp.zm_orth x
    · simp only [patchEv, baseDualHyperbolicVector]
      split_ifs with h3
      · rw [vecY_repr]
        exact (D.sp.hyp_orthX _ x).2
      · rw [vecY_zero]
        first | exact map_zero _ | simp

theorem nfScal_patch_zero (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (i : ℕ) :
    nfScal (patchK κ) (patchS s) 0 i = if i ≤ D.R.rS then 1 else -(D.sp.T : D.host.E) := by
  induction i with
  | zero => simp [nfScal, patchS]
  | succ i ih =>
    show patchK κ 0 i * nfScal (patchK κ) (patchS s) 0 i = _
    rw [ih]
    have hk : patchK κ 0 i = kap0 (D := D) i := if_pos rfl
    rw [hk]
    unfold kap0
    split_ifs <;> first | (exfalso; omega) | simp

theorem nfScal_patch_succ (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (j i : ℕ) :
    nfScal (patchK κ) (patchS s) (j + 1) i = nfScal κ s (j + 1) i := by
  induction i with
  | zero => simp [nfScal, patchS]
  | succ i ih =>
    show patchK κ (j + 1) i * nfScal (patchK κ) (patchS s) (j + 1) i = κ (j + 1) i * nfScal κ s (j + 1) i
    rw [ih]
    simp [patchK]

theorem normalised_adapted_vector_zero (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (i : ℕ) (hi : i < D.R.m - 1) (r : Fin (D.sp.Y 0).rank) :
    nfScal (patchK κ) (patchS s) 0 i * adaptedVector (patchE e) (patchEv ev) (patchZ z) 0 i r = frame0 i r := by
  have hd : (D.R.m - 1 - 0) / 2 = D.R.rS := m_sub_one_div_two
  have hm : (D.R.m - 1 - 0) % 2 = 1 := m_sub_one_mod_two
  rw [nfScal_patch_zero]
  unfold adaptedVector frame0
  rcases lt_trichotomy i D.R.rS with h | h | h
  · rw [if_pos (by omega : i ≤ D.R.rS), if_pos (by omega : i < (D.R.m - 1 - 0) / 2), dif_pos h]
    simp [patchE, baseHyperbolicVector, h]
  · rw [if_pos (by omega : i ≤ D.R.rS), if_neg (by omega : ¬ i < (D.R.m - 1 - 0) / 2),
      if_pos (⟨hm, by omega⟩ : (D.R.m - 1 - 0) % 2 = 1 ∧ i = (D.R.m - 1 - 0) / 2),
      dif_neg (by omega : ¬ i < D.R.rS), if_pos h]
    simp [patchZ, baseLineVector]
  · have hk : D.R.m - 1 - 0 - 1 - i = 2 * D.R.rS - i := by omega
    have h4 : 2 * D.R.rS - i < D.R.rS := by omega
    rw [if_neg (by omega : ¬ i ≤ D.R.rS), if_neg (by omega : ¬ i < (D.R.m - 1 - 0) / 2),
      if_neg (by rintro ⟨-, hc⟩; omega), dif_neg (by omega : ¬ i < D.R.rS), if_neg (by omega : ¬ i = D.R.rS),
      dif_pos h4, hk]
    simp [patchEv, baseDualHyperbolicVector, h4]

theorem val_nfScal_patch_zero (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (PP : Pl D.host.E)
    (hT : ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (i : ℕ) :
    PP.valuation D.host.E (nfScal (patchK κ) (patchS s) 0 i) = 1 := by
  rw [nfScal_patch_zero]
  split_ifs
  · exact map_one _
  · rw [Valuation.map_neg, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    first
      | exact le_antisymm (PP.intValuation_le_one _)
          (not_lt.mp fun h => hT (Ideal.dvd_span_singleton.mp ((PP.intValuation_lt_one_iff_dvd _).mp h)))
      | exact le_antisymm (PP.intValuation_le_one _) (not_lt.mp fun h => hT ((PP.intValuation_lt_one_iff_mem _).mp h))
      | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff PP _).mpr hT

open Classical in

theorem colsAt_zero (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D)) (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E)
    (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (S Pg : Finset (Pl D.host.E))
    (h0 : NormalFrame0 (βY 0) S Pg) :
    ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ColsAt βY (patchE e) (patchEv ev) (patchZ z) (patchK κ) (patchS s) Pg PP ei 0 := by
  have hN : D.R.N 0 = D.R.k := by simp [Formalism.BasicNotions.Ranks.N]
  intro PP hPP ei hei
  obtain ⟨h1, h2⟩ := h0 PP hPP ei hei
  unfold ColsAt
  refine ⟨?_, ?_⟩
  · intro i hi col hcol
    simp only [normalised_adapted_vector_zero e ev z κ s i (by omega)]
    exact h1 i (by omega) col (by rw [hN]; exact hcol)
  · intro col hcol
    rcases hcol with hc | hc
    · exact h2 col (by rw [hN]; exact hc)
    · exfalso
      have hr := D.sp.Y_rank 0 (Nat.zero_le _)
      have hlt := col.isLt
      simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r] at hr
      omega

theorem colsAt_patch_succ (βY : ∀ j : ℕ, GL (Fin (D.sp.Y j).rank) (EAf D))
    (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) (Pg : Finset (Pl D.host.E)) (PP : Pl D.host.E) (ei : AE D) (j : ℕ) :
    ColsAt βY (patchE e) (patchEv ev) (patchZ z) (patchK κ) (patchS s) Pg PP ei (j + 1) ↔
      ColsAt βY e ev z κ s Pg PP ei (j + 1) := by
  have h1 : ∀ i, nfScal (patchK κ) (patchS s) (j + 1) i = nfScal κ s (j + 1) i := fun i => nfScal_patch_succ κ s j i
  simp only [ColsAt, h1]
  try exact Iff.rfl

variable (D) in

def AdaptedVectorsExist : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E),
    ∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j

open Classical in

def LatFramesExist {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧
    (∀ t : T, (∀ PP ∈ Pg ∪ Q t ∪ Sd, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ j, 1 ≤ j → j < D.R.m →
        ColsAt (betaYOf βY) e ev z κ s Pg PP ei j) ∧
      NormalFrame0 (betaYOf βY 0) (Pg ∪ Q t ∪ Sd) Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg

theorem framesExist_of {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (hT : ∀ PP ∈ Pg, ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E)
    (haux : ∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j) (hκ : ∀ j, 1 ≤ j → ∀ i, κ j i ≠ 0)
    (hs : ∀ j, 1 ≤ j → s j ≠ 0)
    (hu : ∀ PP ∈ Pg, ∀ j, 1 ≤ j → j < D.R.m → ∀ i < D.R.m - 1 - j, PP.valuation D.host.E (nfScal κ s j i) = 1)
    (hL : LatFramesExist Pg Sd Q e ev z κ s) : FramesExist D Pg Sd Q := by
  obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, hN, hV⟩ := hL
  refine ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, patchE e, patchEv ev, patchZ z, patchK κ, patchS s,
    fun t => ⟨?_, (hN t).2⟩, hV⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    cases j with
    | zero => exact adapted_relations_at_zero e ev z
    | succ j => exact haux (j + 1) (Nat.succ_pos j) hj
  · intro j i
    cases j with
    | zero =>
      have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero
      simp only [patchK, kap0]
      split_ifs <;> simp_all
    | succ j => simpa [patchK] using hκ (j + 1) (by omega) i
  · intro j
    cases j with
    | zero => simp [patchS]
    | succ j => simpa [patchS] using hs (j + 1) (by omega)
  · intro PP hPP j hj i hi
    cases j with
    | zero => exact val_nfScal_patch_zero κ s PP (hT PP hPP) i
    | succ j =>
      rw [nfScal_patch_succ]
      exact hu PP hPP (j + 1) (by omega) hj i hi
  · intro PP hPP ei hei j hj
    cases j with
    | zero => exact colsAt_zero (betaYOf βY) e ev z κ s _ Pg (hN t).2 PP hPP ei hei
    | succ j => exact (colsAt_patch_succ _ e ev z κ s Pg PP ei j).mpr ((hN t).1 PP hPP ei hei (j + 1) (by omega) hj)

theorem framesExist_of_open {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (hT : ∀ PP ∈ Pg, ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (h : ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
      (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
      (∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j) ∧ (∀ j, 1 ≤ j → ∀ i, κ j i ≠ 0) ∧ (∀ j, 1 ≤ j → s j ≠ 0) ∧
      (∀ PP ∈ Pg, ∀ j, 1 ≤ j → j < D.R.m → ∀ i < D.R.m - 1 - j, PP.valuation D.host.E (nfScal κ s j i) = 1) ∧
      LatFramesExist Pg Sd Q e ev z κ s) : FramesExist D Pg Sd Q := by
  obtain ⟨e, ev, z, κ, s, h1, h2, h3, h4, h5⟩ := h
  exact framesExist_of Pg Sd Q hT e ev z κ s h1 h2 h3 h4 h5

theorem T_notMem_of_typePlaces {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Pl D.host.E)}
    (h : Formalism.IndefR.Lev.IsTypePlaces (D := D) D.host.g pb Pg) :
    ∀ PP ∈ Pg, ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro PP hPP hTmem
  obtain ⟨htd, hPg⟩ := h

  have hab : pb 0 * pb 1 ∈ PP.asIdeal := by
    rw [hPg] at hPP
    unfold Formalism.L2.DIV.primesOf at hPP
    split_ifs at hPP with h0
    · simp at hPP
    · rw [Set.Finite.mem_toFinset] at hPP
      exact Ideal.dvd_span_singleton.mp hPP

  have key : ∀ i, pb i ∈ PP.asIdeal → ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro i hi
    have hc : ((D.host.g i : ℕ) : 𝓞 D.host.E) =
        pb i * NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) (pb i) := by
      apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
      rw [map_natCast, map_mul]
      exact (htd.norm i).symm
    rw [hc]
    exact PP.asIdeal.mul_mem_right _ hi
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hab with h1 | h1
    · exact ⟨0, key 0 h1⟩
    · exact ⟨1, key 1 h1⟩
  obtain ⟨i, hi⟩ := hg

  obtain ⟨π, -, hπT, hπ1⟩ := D.T_norm D.u₀
  have hT' : D.sp.T = (D.mem D.u₀).A.T := D.sp_T
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hπ1
  have hn : ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E) ∈
      PP.asIdeal := by
    have hdv : D.host.g i ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
      apply Dvd.dvd.mul_left
      apply Dvd.dvd.pow _ two_ne_zero
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨k, hk⟩ := hdv
    rw [hk, Nat.cast_mul]
    exact PP.asIdeal.mul_mem_right _ hi
  have hy' : (y : D.host.E) * ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : D.host.E)
      = (π : D.host.E) - 1 := by
    have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hy
    rw [map_mul, map_sub, map_one, map_natCast] at this
    exact this
  have hconj : D.conjF (y : D.host.E) *
      ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : D.host.E)
      = D.conjF (π : D.host.E) - 1 := by
    have := congrArg D.conjF hy'
    rw [map_mul, map_sub, map_one, map_natCast] at this
    exact this
  have hmain : ((D.sp.T : ℕ) : D.host.E) - 1 = ((π : D.host.E) - 1) * D.conjF (π : D.host.E) +
      D.conjF (y : D.host.E) * ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : D.host.E) := by
    rw [hconj, hT', ← hπT, D.conjF_eq]
    ring
  have hmem : ((D.sp.T : ℕ) : 𝓞 D.host.E) - 1 =
      (π - 1) * NumberField.RingOfIntegers.mapRingHom D.conjF.toRingHom π +
        NumberField.RingOfIntegers.mapRingHom D.conjF.toRingHom y *
          ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E) := by
    apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
    rw [map_sub, map_one, map_natCast, map_add, map_mul, map_mul, map_sub, map_one, map_natCast]
    exact hmain
  have h1 : ((D.sp.T : ℕ) : 𝓞 D.host.E) - 1 ∈ PP.asIdeal := by
    rw [hmem]
    refine PP.asIdeal.add_mem (PP.asIdeal.mul_mem_right _ ?_) (PP.asIdeal.mul_mem_left _ hn)
    rw [← hy]
    exact PP.asIdeal.mul_mem_left _ hn
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h2 := PP.asIdeal.sub_mem hTmem h1
  rwa [sub_sub_cancel] at h2

theorem framesExist_of_typePlaces {T : Type} {pb : Fin 2 → 𝓞 D.host.E} (Pg Sd : Finset (Pl D.host.E))
    (Q : T → Finset (Pl D.host.E)) (hPg : Formalism.IndefR.Lev.IsTypePlaces (D := D) D.host.g pb Pg)
    (h : ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
      (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
      (∀ j, 1 ≤ j → j < D.R.m → IsHyperbolicFrameAt e ev z j) ∧ (∀ j, 1 ≤ j → ∀ i, κ j i ≠ 0) ∧ (∀ j, 1 ≤ j → s j ≠ 0) ∧
      (∀ PP ∈ Pg, ∀ j, 1 ≤ j → j < D.R.m → ∀ i < D.R.m - 1 - j, PP.valuation D.host.E (nfScal κ s j i) = 1) ∧
      LatFramesExist Pg Sd Q e ev z κ s) : FramesExist D Pg Sd Q :=
  framesExist_of_open Pg Sd Q (T_notMem_of_typePlaces hPg) h

end Formalism.IndefR.Seed.Frm

end
