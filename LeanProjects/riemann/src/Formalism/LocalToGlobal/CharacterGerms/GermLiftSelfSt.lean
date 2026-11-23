import Formalism.LocalToGlobal.CharacterGerms.RowTieValG
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

abbrev IS (I0 : Orb → Type) : Orb → Fin 2 → Type := fun o _ => I0 o

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def uS (w : WVO (IS I0)) : Fin 2 × Fin dd → C := (Y.rawSelf (p w.1)).u w.2.1 w.2.2

def pull2 (F : PS C 2 dd) : MvPowerSeries (WVO (IS I0)) C := VP.linPull Y (uS Y p) F

def MS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (x : Fin N × WVO (IS I0)) (q : Fin n × Fin dd) : C :=
  ∑ col : Fin 2, if pl (x.1, col) = q.1 then uS Y p x.2 (col, q.2) else 0

def pullS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : PS C n dd) : MvPowerSeries (Fin N × WVO (IS I0)) C :=
  VP.linPull Y (MS Y p pl) F

def UnitSelfSt : Prop :=
  SelfSep Y p → ∃ U : PS C 2 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)

def GermLiftSelfSt (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g))
    (t : ∀ _ : Fin 2, I0 o → MvPowerSeries (I0 o) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 2 dd, IntS V G ∧ pull2 Y p G = toAllS (I := IS I0) o F

end Defs

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem MS_pl (ρ' ρ : Fin N) (w : WVO (IS I0)) (col : Fin 2) (i : Fin dd) :
    MS Y p pl (ρ', w) (pl (ρ, col), i) = if ρ' = ρ then uS Y p w (col, i) else 0 := by
  simp only [MS, pl.injective.eq_iff, Prod.mk.injEq]
  by_cases h : ρ' = ρ
  · simp [h]
  · simp [h]

theorem MS_off (x : Fin N × WVO (IS I0)) (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) :
    MS Y p pl x (b, i) = 0 := by
  simp only [MS]
  exact Finset.sum_eq_zero fun col _ => if_neg fun h => hb ⟨_, h⟩

theorem linPt_pl (ρ : Fin N) (col : Fin 2) (i : Fin dd) :
    linPt Y (MS Y p pl) (pl (ρ, col), i) = rowOf ρ (linPt Y (uS Y p) (col, i)) := by
  simp only [linPt]
  rw [rowOf_eq, rename_subst_linS]
  congr 1
  funext j
  simp only [linS, colLin, map_sum, map_smul, MvPowerSeries.rename_X]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
  · simp only [MS_pl, if_true]
    rfl
  · intro ρ' _ hρ'
    simp [MS_pl, hρ']
  · simp

theorem linPt_off (b : Fin n) (hb : b ∉ Set.range pl) (i : Fin dd) : linPt Y (MS Y p pl) (b, i) = 0 := by
  have h0 : linS (colLin (MS Y p pl) b) = 0 := by
    funext j
    simp [linS, colLin, MS_off Y p pl _ b hb]
  have hc := cc_linPt Y (MS Y p pl) (b, i)
  simp only [linPt, h0, MvPowerSeries.subst_zero_eq_C_constantCoeff] at hc ⊢
  simp at hc
  simp [hc]

theorem cc_ptPl (ρ : Fin N) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  obtain ⟨c, i⟩ := q
  fin_cases c <;> simp [pt]

theorem pullS_plane (ρ : Fin N) (G : PS C 2 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] G) = rowOf ρ (pull2 Y p G) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_ptPl pl ρ q)
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hL2 hR]
  congr 1
  funext ⟨c, i⟩
  have hc : (![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] : Fin 2 → Pt C n dd) c i =
      MvPowerSeries.X (pl (ρ, c), i) := by
    fin_cases c <;> rfl
  rw [hc, MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_col (ρ : Fin N) (col : Fin 2) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd (pl (ρ, col))] E) = rowOf ρ (pull2 Y p (ev (n := 2) ![pt C dd col] E)) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd (pl (ρ, col))] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hA' : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hL2 : MvPowerSeries.HasSubst (linPt Y (uS Y p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  have hR : MvPowerSeries.HasSubst (fun w : WVO (IS I0) =>
      (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WVO (IS I0)) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hcol : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => linPt Y (uS Y p) (col, q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ _)
  have hin : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (uS Y p))
      ((![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2)) = fun q => linPt Y (uS Y p) (col, q.2) := by
    funext ⟨c, i⟩
    fin_cases c
    exact MvPowerSeries.subst_X hL2 (col, i)
  simp only [pullS, pull2, linPull, ev, rowOf]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL, MvPowerSeries.subst_comp_subst_apply hA' hL2, hin,
    MvPowerSeries.subst_comp_subst_apply hcol hR]
  congr 1
  funext ⟨c, i⟩
  have hc0 : c = 0 := Subsingleton.elim _ _
  subst hc0
  change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (pl (ρ, col), i)) =
    MvPowerSeries.subst (fun w => MvPowerSeries.X (ρ, w)) (linPt Y (uS Y p) (col, i))
  rw [MvPowerSeries.subst_X hL, linPt_pl]
  rfl

theorem pullS_off (b : Fin n) (hb : b ∉ Set.range pl) (E : PS C 1 dd) :
    pullS Y p pl (ev (n := n) ![pt C dd b] E) = MvPowerSeries.C (MvPowerSeries.constantCoeff E) := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by obtain ⟨c, i⟩ := q; fin_cases c; simp [pt])
  have hL : MvPowerSeries.HasSubst (linPt Y (MS Y p pl)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => cc_linPt Y _ q)
  simp only [pullS, linPull, ev]
  rw [MvPowerSeries.subst_comp_subst_apply hA hL]
  have h0 : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (linPt Y (MS Y p pl))
      ((![pt C dd b] : Fin 1 → Pt C n dd) q.1 q.2)) = 0 := by
    funext ⟨c, i⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    subst hc0
    change MvPowerSeries.subst (linPt Y (MS Y p pl)) (MvPowerSeries.X (b, i)) = 0
    rw [MvPowerSeries.subst_X hL, linPt_off Y p pl b hb i]
  rw [h0, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem hco_of_img {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (ℓ : ι)
    (co : Fin N × WVO (IS I0) → C)
    (h : ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : WVO (IS I0), co (ρ, w) • (Y.rawSelf (p w.1)).u w.2.1 w.2.2) (b : Fin n) (i : Fin dd) :
    ∑ x, co x * MS Y p pl x (b, i) = if b = cp ℓ then uv ℓ i else 0 := by
  obtain ⟨ρ, col, hpl, hco0, hvec⟩ := h
  have key : ∀ c : Fin 2, (∑ x : Fin N × WVO (IS I0),
      co x * (if pl (x.1, c) = b then uS Y p x.2 (c, i) else 0)) =
      if pl (ρ, c) = b then (if c = col then uv ℓ i else 0) else 0 := by
    intro c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ
      (fun ρ' _ hρ' => Finset.sum_eq_zero fun w _ => by simp [hco0 ρ' w hρ']) (by simp)]
    by_cases hb' : pl (ρ, c) = b
    · have h1 := congrFun hvec (c, i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [hb', if_true]
      rw [h1]
      rfl
    · simp [hb']
  simp only [MS, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single col (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true]
  by_cases hb : b = cp ℓ
  · simp [hb, hpl]
  · have h2 : pl (ρ, col) ≠ b := fun h' => hb (h'.symm.trans hpl)
    simp [h2, hb]

end VP

end Formalism.L2.FormalSeriesBounds
