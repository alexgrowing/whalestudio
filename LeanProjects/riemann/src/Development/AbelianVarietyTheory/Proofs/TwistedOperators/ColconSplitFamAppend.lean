import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.Unf

theorem colcon_splitFam_append {T : Type} {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : p.Fam S) (e : q.Fam S), splitFam q (Path.Fam.append (q := q) d e) = (d, e)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
      show ((splitFam q (Path.Fam.append (q := q) d e.1)).1, ((splitFam q (Path.Fam.append (q := q) d e.1)).2, e.2)) = (d, e)
      rw [colcon_splitFam_append q d e.1]
      rfl

theorem colcon_getD_downFam {T : Type} {S : Arrow T → Type} (t : T) (i : ℕ) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, S (.down t i j)) (j : ℕ) (hj : j < n), getD t i n (downFam t i n f) j hj = f ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, j, hj => by
      unfold getD
      have hs := colcon_splitFam_append (p := Path.one (.down t i n)) (downPath t i n) ((), f (Fin.last n))
        (downFam t i n fun j => f j.castSucc)
      rw [downFam]
      split_ifs with h
      · erw [hs]
        exact colcon_getD_downFam t i n _ j h
      · obtain rfl : n = j := by omega
        erw [hs]
        rfl

theorem colcon_nIter_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) {q q' : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), NIter ρ μ q l h z →
      (∀ h' : ∀ i, H i, (∀ i, i ∉ l → h' i = h i) → q h' = q' h') → NIter ρ μ q' l h z
  | [], h, z, hz, hq => (show z = q h from hz).trans (hq h fun _ _ => rfl)
  | i :: l, h, z, ⟨f, hf, hr⟩, hq => ⟨f, hf, fun g => colcon_nIter_congr ρ μ l _ _ (hr g) fun h' hh' => hq h' fun k hk => by
      rw [hh' k fun hl => hk (List.mem_cons_of_mem _ hl), Function.update_of_ne fun e => hk (by simp [e])]⟩

theorem colcon_quot {G : Type} [Group G] [MeasurableSpace G] {R R' : Subgroup G} (e : R = R') {ρ : Measure R} {ρ' : Measure R'}
    (hh : HEq ρ ρ') {μ : Measure G} {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 ρ' μ f z) : IsQuotIntL1 ρ μ f z := by
  subst e
  obtain rfl := eq_of_heq hh
  exact h

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem colcon_rowGrp_jac {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (jacAt G hM j σ hj).d := by
  unfold rowGrp
  rw [dif_pos (by omega)]
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  rfl

theorem colcon_rowGrp_bes {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m)
    (vN : VolN (besDecAt G j σ hj)) :
    rowGrp G j = besGrp (besAt G hM j σ hj vN).d (besAt G hM j σ hj vN).o := by
  unfold rowGrp
  rw [dif_neg (by omega), dif_pos (by omega)]
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  rfl

theorem colcon_gen (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t)
    (F : Fn G (.grid D.R.m D.R.m)) (ρ : ∀ j, Measure (rowGrp G j))
    (hJ : ∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR)
    (hB : ∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) (h : Pts G) (g : GA D (G.V (.grid D.R.m j)))
      (φ : GA D (G.V (.top j)) → ℂ) (z : ℂ), g = h j →
      (chainFrom G W t hM σ j hj vN).Iter
        (colPer W hM σ j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) σ j hj vN) F φ g) z →
      NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h' => jPer W M t (conAt W hM Φ h') F σ j hj φ)
        (List.range' (j + 1) (2 * σ)) h z
  | 0, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hc : conAt W hM Φ h j = lastDat W hM j hj vN (h j) (Φ ⟨j, by omega⟩)
          (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := by
        unfold conAt
        rw [dif_pos hj]
        rfl
      have hz' : z = colPer W hM 0 j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) 0 j hj vN) F φ (h j) () := hz
      show z = jPer W M t (conAt W hM Φ h) F 0 j hj φ
      rw [hz']
      show _ = ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (conAt W hM Φ h j)
        (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
      rw [hc]
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom]
      rw [colcon_getD_downFam, colcon_getD_downFam]
      rfl
  | σ + 1, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      obtain ⟨f₁, f₂, h1, h2⟩ := hz
      have hl : List.range' (j + 1) (2 * (σ + 1)) = (j + 1) :: (j + 1 + 1) :: List.range' (j + 1 + 1 + 1) (2 * σ) := by
        rw [show 2 * (σ + 1) = 2 * σ + 1 + 1 by ring, List.range'_succ, List.range'_succ]
      rw [hl]
      refine ⟨f₁, colcon_quot (colcon_rowGrp_jac hM (j + 1) (σ + 1) (by omega)) (hJ _ _ _) h1, fun a => ?_⟩
      refine ⟨f₂ a, colcon_quot (colcon_rowGrp_bes hM (j + 1 + 1) σ (by omega) _) (hB _ _ (by omega)) (h2 a).1,
        fun b => ?_⟩
      have hi := (h2 a).2 b
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom] at hi
      have ih := colcon_gen G W t hM Φ F ρ hJ hB σ (j + 1 + 1) (by omega) _
        (Function.update (Function.update h (j + 1) a) (j + 1 + 1) b) b _ (f₂ a b) (by simp) hi
      refine colcon_nIter_congr _ _ _ _ _ ih fun h' hh' => ?_
      have e0 : h' j = h j := (hh' j (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _))
      have e1 : h' (j + 1) = a := (hh' (j + 1) (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_self _ _ _))
      have e2 : h' (j + 1 + 1) = b := (hh' (j + 1 + 1) (by simp only [List.mem_range'_1]; omega)).trans (Function.update_self _ _ _)
      show _ = jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) _ (biL W M t j φ (conAt W hM Φ h' j))
      congr 1
      have hx : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
      have hC : conAt W hM Φ h' j = _ :=
        (dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)).trans (dif_pos hx)
      rw [hC]
      obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
      rw [e0, e1, e2, colcon_getD_downFam, colcon_getD_downFam]
      rfl

theorem nIter_conAt_of_colPer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t) (F : Fn G (.grid D.R.m D.R.m)) (φ : Fn G (.top 0)) (z : ℂ), (chain G W t hM).Iter (colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downFam t D.R.m D.R.m Φ)) F φ 1) z → ∀ (ρ : ∀ j, Measure (rowGrp G j)), (∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR) → (∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) → NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h => jPer W M t (conAt W hM Φ h) F _ 0 top_idx φ) (idx D) 1 z := by
  intro D T L sc G W t M hM Φ F φ z hz ρ hJ hB
  have e : List.range' (0 + 1) (2 * ((D.R.m - 2) / 2)) = idx D := by
    unfold idx
    have := top_idx (D := D)
    congr 1
    omega
  rw [← e]
  exact colcon_gen G W t hM Φ F ρ hJ hB _ 0 top_idx (topVN hM) 1 1 φ z rfl hz

end GlobalTheory.RowVal
