import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} (X : TermTie D)

theorem tie_Tu_pos (D : D7) (u : D.what₂.Word) : 0 < Tu D u := (D.mem u).A.T_prime.pos

theorem tie_Gval_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) :
    Gval (X.fl t) (X.fl' t) ≠ 0 := by
  rw [← X.G_eq t]
  exact (map_ne_zero _).2 h

theorem tie_G_pos {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) (τ : D.host.E →+* ℂ) :
    0 < (τ (Gval (X.fl t) (X.fl' t))).re :=
  (b_G_pos (p_starConj D) (tie_Tu_pos D u) (X.fl t) (X.fl' t) (X.fixed t).2.2.1.2 (X.lift' t).2
    (tie_Gval_ne X t h) (p_posX D _ (tie_Tu_pos D u) (X.fl t)) τ).1

theorem GDr_of_tie : PX.GDr D X := by
  intro u u' t h
  have hpos := tie_G_pos X t h
  refine ⟨fun h1 => ?_, fun _ τ => hpos _⟩

  have hG : Gval (X.fl t) (X.fl' t) = -(((Tu D u : ℕ) : D.host.E) * ((Tu D u' : ℕ) : D.host.E) *
      (Dl (X.fl t).fl (X.fl' t).fl D.R.rS * star (Dl (X.fl t).fl (X.fl' t).fl D.R.rS))) := by
    simp only [Formalism.MainNotions.S.Lat.Gval, Formalism.MainNotions.S.Gflag, h1, star_zero, mul_zero, zero_sub]
  haveI := D.host.isCMField_hostE
  have hc : ∀ y : D.host.E, D.host.φ₀ (star y) = starRingEnd ℂ (D.host.φ₀ y) := fun y =>
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ y
  have h0 := hpos D.host.φ₀
  rw [hG, map_neg, map_mul, map_mul, map_mul, map_natCast, map_natCast, hc, Complex.mul_conj] at h0
  have key : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
      Complex.normSq (D.host.φ₀ (Dl (X.fl t).fl (X.fl' t).fl D.R.rS)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
  simp at h0
  linarith

theorem S0ge1_of_tie (X : TermTie D) : PX.FirstSumAtLeastOne D := by
  intro u u' p h1 _
  rw [X.s0_eq p]
  unfold Lat.s0
  have hr : finrank D.host.E (Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))) = D.R.k - 1 :=
    a_rankHp_k _ (X.fixed _).1 _ _ (X.fixed _).2.2.1.2 (X.lift' _).2 (tie_Gval_ne X _ h1) D.R.k (p_rankV D)
  have hle : Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) ≤
      Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) := by
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    exact hab.1.1.1
  have h2 := Submodule.finrank_mono hle
  have hk := D.R.m_add_three_le_k
  omega

end Rec

theorem tie_Dl_eq' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) (hj : j ≤ r + 1) :
    Dl F F' j = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  rw [dif_pos hj]

section Packets

variable {D : D7} (X : TermTie D)

theorem tie_X_le_ker {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (y : S.V) (h : ∀ a, S.hT (F.e a) y = 0) : ∀ x ∈ F.X, S.hT x y = 0 := by
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h a
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

theorem tie_Xa_le_X {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem tie_isId_inS (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.isId t) : D.s.inS t := by
  obtain ⟨n, hn, he, hz⟩ := (X.isId_iff t).1 h
  obtain ⟨_, hj, hw⟩ := hn
  refine (X.inS_iff t).2 ⟨fun a => ?_, ?_⟩
  · have hea : (X.fl t).fl.e a ∈ Submodule.span D.host.E ((X.fl t).fl.e '' {i | i.1 < a.val + 1}) :=
      Submodule.subset_span ⟨a, by simp, rfl⟩
    have ha := hj a.val _ hea
    rw [he a] at ha
    exact ha
  · have hzo : (X.fl t).fl.z ∈ orth _ (Xsp (X.fl t)) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      exact tie_X_le_ker (X.fl t).fl _ (X.fl t).fl.z_orth
    have hd : (X.fl' t).fl.z - (X.fl t).fl.z =
        (n (X.fl t).fl.z - (X.fl t).fl.z) - (n (X.fl t).fl.z - (X.fl' t).fl.z) := by abel
    rw [hd]
    exact Submodule.sub_mem _ (hw _ hzo) hz

private theorem Zhat_castSucc_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (he : ∀ a, F'.e a - F.e a ∈ F.Xa a.val)
    (hz : F'.z - F.z ∈ F.X) (a : Fin r) (b : Fin (r + 1)) : Zhat F F' (Fin.castSucc a) b = 0 := by

  have hker : ∀ v ∈ F.X, S.hT (F.e a) v = 0 := by
    intro v hv
    unfold Formalism.MainNotions.S.FlagG.X at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact F.e_iso a c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  induction b using Fin.lastCases with
  | last =>
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]
    rw [show F'.z = F.z + (F'.z - F.z) by abel, map_add, F.z_orth a, hker _ hz, add_zero]
  | cast b =>
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    rw [show F'.e b = F.e b + (F'.e b - F.e b) by abel, map_add, F.e_iso a b,
      hker _ (tie_Xa_le_X F _ (he b)), add_zero]

private theorem Gflag_eq_zero_of_sub_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    {T : E} (F F' : FlagG S r T) (he : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (hz : F'.z - F.z ∈ F.X)
    (hT : star T = T) : Gflag F F' = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hzz : F'.z = F.z := by
      have h0 : F.X = ⊥ := by
        unfold Formalism.MainNotions.S.FlagG.X
        rw [Set.range_eq_empty, Submodule.span_empty]
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hz
      exact hz
    have kF : ∀ i : Fin (0 + 1), F.fvec i = F.z := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      | cast i => exact i.elim0
    have kF' : ∀ i : Fin (0 + 1), F'.fvec i = F'.z := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      | cast i => exact i.elim0
    have h1 : Dl F F' 1 = -T := by
      rw [tie_Dl_eq' F F' 1 le_rfl, Matrix.det_unique]
      simp only [Matrix.submatrix_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, kF, kF']
      rw [hzz, F.z_norm]
    have h2 : Dl F F' 0 = 1 := by
      rw [tie_Dl_eq' F F' 0 (Nat.zero_le _), Matrix.det_isEmpty]
    simp only [Formalism.MainNotions.S.Gflag, zero_add, h1, h2, star_neg, hT, star_one]
    ring
  · have hrow : ∀ (l : ℕ) (hl : l ≤ r + 1) (h0 : 0 < l), Dl F F' l = 0 := by
      intro l hl h0
      rw [tie_Dl_eq' F F' l hl]
      refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h0⟩ (fun j => ?_)
      rw [Matrix.submatrix_apply]
      have hc : (Fin.castLE hl ⟨0, h0⟩ : Fin (r + 1)) = Fin.castSucc ⟨0, hr⟩ := Fin.ext rfl
      rw [hc]
      exact Zhat_castSucc_eq_zero F F' he hz ⟨0, hr⟩ _
    unfold Formalism.MainNotions.S.Gflag
    rw [hrow (r + 1) le_rfl (Nat.succ_pos r), hrow r (Nat.le_succ r) hr]
    simp

theorem term_in_S_vanishes (X : TermTie D) {u : D.what₂.Word} (t : D.s.Term u u) (h : D.s.inS t) : D.s.Gterm t = 0 := by
  obtain ⟨he, hz⟩ := (X.inS_iff t).1 h
  have hG : Gval (X.fl t) (X.fl' t) = 0 :=
    Gflag_eq_zero_of_sub_mem (X.fl t).fl (X.fl' t).fl he hz (by simp)
  have h2 := X.G_eq t
  rw [hG] at h2
  exact (map_eq_zero_iff _ (algebraMap _ _).injective).1 h2

end Packets

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma

end
