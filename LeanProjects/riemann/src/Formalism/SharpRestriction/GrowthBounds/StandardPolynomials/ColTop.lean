import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialSumEqProd
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDChain
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXNum
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXPH
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSum

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.ColF Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

theorem col_lamS_vec {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1)) : (lamS X j a.succ).2 = (L.LL j).vec a := by
  show _ = decide ((a : ℕ) % 2 = 0)
  by_cases h : (a : ℕ) < 2 * segS X.TT j
  · rw [lamS_succ_lt X j a h]
  · rw [lamS_succ_ge X j a h]
    have : (a : ℕ) = 2 * segS X.TT j := by have := a.2; omega
    simp [this]

theorem column_kappa_nonneg (X : Loc) : 0 ≤ ka1 X := by
  unfold ka1 Loc.k Loc.Q
  positivity

theorem colsAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hNum : ColumnNumericsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hS hD hH hC mm hmm n hn1 hnc β hβ L j y hy
  obtain ⟨hnum1, hnum2⟩ := hNum X hD hH hC mm hmm n hn1 hnc j (β j) (hβ j)
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  have hG : segG X.TT j ≤ X.G' := (hH.1.2.2.2.2.1 j).1
  have hs : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hN : 2 * X.N1 + 2 ≤ X.m := hH.1.2.2.2.2.2.2.1
  have hm : 2 * segS X.TT j + 1 < X.m := by omega
  have hn' : 1 ≤ X.n' := by have := hD.2.2.1; omega
  have hp : 0 < X.p := hD.1.pos
  have h := ph_seg L j y hy (hβ j) hnum1 hnum2 hm
  have hvec := col_lamS_vec L j
  have hmu : 0 ≤ mm + (n : ℝ) * ka1 X := by
    have h1 : 0 ≤ mm := by
      rcases hmm with h | h
      · rw [h]
      · rw [h]; positivity
    have h3 := column_kappa_nonneg X
    positivity
  exact ⟨{
    ι := ↥(colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
    fin := inferInstance
    Kc := fun c => Kcol (KK O) y.1.1.mu c.1 (2 * segS X.TT j + 1) (y.1.2 c.1)
    dK := fun c => dKS X j y.1.1.mu c.1
    pl := fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c.1
    fC := fun c => fCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu O y.1.2 c.1
    oC := fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    dgC := fun c => dgCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    a0 := (a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).toNat
    KInt := fun c => colKInt y.1.1.mu c.1 _
    KPol := fun c => colKPol j y.1.1.mu c.1 _
    digit_le_one := fun c i => by unfold dKS; split_ifs <;> omega
    dKsum := fun i => by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu) (fun c => dKS X j y.1.1.mu c i)]
      exact dKsum_seg L j y h i
    Kprod := by
      rw [Finset.prod_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => Kcol (KK O) y.1.1.mu c (2 * segS X.TT j + 1) (y.1.2 c))]
      exact Kprod_seg L j y (KK O)
    facC := fun c => colFac j y.1.1.mu y.1.2 S hS hn' h2 h hvec c.1
    homC := fun c => colHomC j y.1.1.mu h (fun a => (hvec a).symm) c.1 _
    fPol := fun c => colFPol j y.1.1.mu h2 y.1.2 c.1
    polC := fun c => colPolC j y.1.1.mu h c.1 _
    plQ := fun c l => colPlQ j hp h2 hG c.1 l
    dgCQ := fun c l => colDgQ j y.1.1.mu hp h2 hG c.1 l
    dgCY := fun c j' => colDgY j y.1.1.mu c.1 j'
    a0le := by
      have h0 : 0 ≤ a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j := sub_nonneg.2 hnum1
      rw [Int.toNat_of_nonneg h0]
      unfold a0Z
      rw [sub_add_cancel]
      have h1 : ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ)⌋ := Int.floor_le_floor (by linarith)
      rwa [Int.floor_intCast] at h1
    plSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c)]
      exact plSum_seg L j y h
    oSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c)]
      exact oSum_seg L j y h }⟩

theorem restCols : RestCols :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => colsAt_of h) column_numerics_holds

end Formalism.MainNotions.ColumnSystems.Pf
