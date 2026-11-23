import Formalism.LocalToGlobal.GlobalTheory.PlacesP

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.HN Formalism.LFunctionChainParameters

theorem level_prime_division_of_statements {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (tSet : SettingEventually Fm) (hTu : TuSize Fm) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, h0⟩ := h10
  obtain ⟨x1, h1⟩ := tSet
  refine J.family_levelPrime_summary_closed Fm crystallineComparison hTu (dlSize eps Fm) ⟨max (max x0 x1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  exact ⟨fun u => (h0 x hx0 i u (h1 x hx1 hx2 i u)).2.1, fun u => (h0 x hx0 i u (h1 x hx1 hx2 i u)).2.2.2.2.1⟩

theorem placesF_min' {eps : ℝ} (Fm : FamP eps) (h26 : LocalQuadraticParts.LevelTFamily Fm) (hNC : Lnk.NuCommensF Fm) (hTu : TuSize Fm)
    (hRank : J.MuRank Fm) (lG : LinkG Fm) (lMu : LinkMu Fm) : Lnk.PlacesF Fm := by
  have heps := Lnk.fam_eps_pos Fm
  obtain ⟨xNC, hNC⟩ := hNC
  obtain ⟨CT, xT, δ, hδ, hTa⟩ := G.TopChoiceBounds.tau_sum_family_of_mertens Fm (fun _ _ => mertens)
  obtain ⟨C26, x26, h26⟩ := h26
  obtain ⟨CMu, xMu, hMu⟩ := lMu
  obtain ⟨CG, xG, δG, -, hG⟩ := lG
  obtain ⟨xR, hRank⟩ := hRank
  obtain ⟨xU, hTu⟩ := hTu
  obtain ⟨xE, hE⟩ := Lnk.ev_pow_le_exp 1 eps 9 one_pos heps
  obtain ⟨xM, hM⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 6
  obtain ⟨xD, hD⟩ : ∃ xD : ℝ, ∀ x ≥ xD, δ x ≤ 1 :=
    Filter.eventually_atTop.1 (hδ.eventually (Iic_mem_nhds zero_lt_one))
  refine ⟨max (max C26 CMu) 4,
    |xNC| + |xT| + |x26| + |xMu| + |xG| + |xR| + |xU| + |xE| + |xM| + |xD| + |Fm.x1| + 4 * |CT| + 5,
    le_max_right _ _, fun x hx i => ?_⟩
  have n1 := abs_nonneg xNC
  have n2 := abs_nonneg xT
  have n3 := abs_nonneg x26
  have n4 := abs_nonneg xMu
  have n5 := abs_nonneg xG
  have n6 := abs_nonneg xR
  have n7 := abs_nonneg xU
  have n8 := abs_nonneg xE
  have n9 := abs_nonneg xM
  have n10 := abs_nonneg xD
  have n11 := abs_nonneg Fm.x1
  have n12 := abs_nonneg CT
  have e1 : x ≥ xNC := by linarith [le_abs_self xNC]
  have e2 : x ≥ xT := by linarith [le_abs_self xT]
  have e3 : x ≥ x26 := by linarith [le_abs_self x26]
  have e4 : x ≥ xMu := by linarith [le_abs_self xMu]
  have e5 : x ≥ xG := by linarith [le_abs_self xG]
  have e6 : x ≥ xR := by linarith [le_abs_self xR]
  have e7 : x ≥ xU := by linarith [le_abs_self xU]
  have e8 : x ≥ xE := by linarith [le_abs_self xE]
  have e9 : xM ≤ x := by linarith [le_abs_self xM]
  have e10 : x ≥ xD := by linarith [le_abs_self xD]
  have hx1 : Fm.x1 < x := by linarith [le_abs_self Fm.x1]
  have hx5 : 5 ≤ x := by linarith
  have hxC : 4 * |CT| + 1 ≤ x := by linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have S := Fm.sizes x hx1 i
  have hb9 : (Fm.L x i).sc.x ^ 9 ≤ (Fm.L x i).sc.b := by
    have h := hE x e8 (by linarith)
    rw [one_mul] at h
    unfold Scale.b Scale.L
    rw [hsx, hse, ← Real.rpow_natCast x 9]
    exact_mod_cast h
  have hx5' : 5 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx5
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := sizes_at (Fm.L x i) S hx5' hb9
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by linarith
  have hm6 : (6 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) S (by linarith)).1
    rw [hsx] at z1
    exact le_trans (hM x e9) z1
  have hTb : ∀ u, (Fm.L x i).sc.b ^ 3 ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    refine le_trans ?_ ((hTu x e7 i).1 u)
    rw [← Real.rpow_natCast (Fm.L x i).sc.b 3]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    push_cast
    linarith
  have hXT : ∀ u, (Fm.L x i).sc.X' ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    have h3 : (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ^ 3 := by
      have : (Fm.L x i).sc.b ^ 3 = (Fm.L x i).sc.b * (Fm.L x i).sc.b ^ 2 := by ring
      rw [this]
      have h2 : (1 : ℝ) ≤ (Fm.L x i).sc.b ^ 2 := one_le_pow₀ hb1
      nlinarith
    linarith [hTb u]
  have hsz := fun u => size_alt ((Fm.D x i).R.f : ℝ) (Fm.L x i).sc.b (((Fm.D x i).mem u).A.T : ℝ)
    (Nat.cast_nonneg _) s8 s9 (hTb u)
  have hfill := Fm.fills x hx1 i
  refine ⟨Lnk.IOsum_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def
    (fun w => (hfill w).2.2.2.2.2.1), ?_⟩
  refine places_at_of C26 CMu _ (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _)) (Fm.nprimeDef x hx1 i) (Fm.nuDef x hx1 i) (hNC x e1 i)
    (hRank x e6 i) (h26 x e3 i) (hMu x e4 i)
    (fun u w hw => ⟨((hG x e5 i).1 u w hw).1, ((hG x e5 i).1 u w hw).2.1⟩)
    (fun w => by rw [(hfill w).2.2.2.2.1]; exact exists_tau_eq_natCast _ _ _ _ _)
    (fun w => by
      rw [(hfill w).2.2.2.2.2.1]
      exact Lnk.ioP_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def _ _ _)
    (fun u w hw => by
      rw [(hfill w).2.2.2.2.1, hw]
      exact tau_eq_zero_of_le _ _ _ _ _ (hXT u))
    (fun u w hs => ?_)
    (ta_le (Fm.L x i) S hx5' hb9 CT (δ x) (by rw [hsx]; exact hxC) (hD x e10) (hTa x e2 i))
    (fun u => (hsz u).1) (fun u => (hsz u).2.1) (fun u => (hsz u).2.2)
  by_cases hw : (Fm.D x i).what₂.places.resChar w = ((Fm.D x i).mem u).A.T
  · exact Or.inl (lenLoc_atT_zero (Fm.ex x hx1 i).lat.atT (Fm.ex x hx1 i).err.edef u w hw hs)
  · refine Or.inr (Fm.lats0 x hx1 i w u (VV_empty_of_ge _ _ _ _ _ ?_) hw)
    have h1 : ¬ ((((Fm.D x i).what₂.places.resChar w : ℕ) : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) :=
      fun h => hs (Fm.supp_sat x hx1 i w h)
    linarith [not_le.1 h1]

theorem placesF_of_via_min : PlaceConditionsFamily := by
  exact placesF_of

end Formalism.L2.GlobalTheoryTheory.Places

end
