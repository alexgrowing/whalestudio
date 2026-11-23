import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Min

variable (D : D7) (u : D.what₂.Word)

def HeckeIntegralLevelZero : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) ∧
    Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v)

def HeckeRamifiedLevelZero : Prop :=
  ∀ v, ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
    Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ

def SecondBranchInclusionLength : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)))

variable {D u}

theorem secondBranchInclusionLength_of_lemB (hB : LemB D u) : SecondBranchInclusionLength D u := by
  unfold LemB at hB
  intro w hw hs v hb
  exact (hB w hw hs v).2 hb

theorem rational_level_zero_of_integral (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (h4 : HeckeIntegralLevelZero D u) :
    Rat0 D u := fun v =>
  ⟨rat_of_into w _ _ _ (h4 w hw hs v).1 ((D.fm u).Bw_span 0 w v),
    rat_of_into w _ _ _ (h4 w hw hs v).2 (S_span 0 w)⟩

theorem hecke_ramified_lattice_stable_length (hS : HidaSetting D u) (hR : Rat0 D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u)
    (w : D.what₂.places.Pl) (hw : OverT D u w) {v : (D.mem u).A.vT} (hv : v ∈ VV D u w) :
    (Sram D u w).map (gR hR w v) ≤ Sram D u w ∧
    ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)) ∧
      Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v)).comap (Sram D u w).subtype) ≤
        ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) := by
  obtain ⟨hs, ht⟩ := mem_VV hv
  have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) := hS.2.2 _ ht
  have hnb : ((nb D u w v : ℕ) : ℤ) = (D.fm u).bTop ((D.fm u).tauOf w v) := Int.toNat_of_nonneg hb
  obtain ⟨hUB, hDS⟩ := h4 w hw hs v
  obtain ⟨a1, n, a2, a3⟩ := hB w hw hs v hb
  rw [← hnb, tL_eq_map] at a1 a2
  have ram := h9 v
  refine ⟨?_, n, a3, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxB : (((D.mem u).A.T : ℕ) : Ow D w) ^ nb D u w v • x ∈ (D.fm u).Bw 0 w v := a1 ⟨x, hx.1, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hUB _ hxB
    have e : gR hR w v x = y := by
      apply (D.fm u).emb_inj 0
      rw [hy', gR_spec, emb_smulR, map_smul]; simp
    rw [e]
    refine ⟨hy, mem_ramSub.mpr ?_⟩
    rw [← e, gR_spec]
    exact Submodule.smul_mem _ _ (ram _ (mem_ramSub.mp hx.2)).1
  · have h := LemmaC_core hR w hw v (nb D u w v) (fun x hx => a1 ⟨x, hx, rfl⟩) hUB hDS ram
    unfold len at a2
    rw [a2] at h
    exact_mod_cast h

theorem congruence_no_kernel_minimal (hS : HidaSetting D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u) :
    CongruenceLatticeLengthBound D u := by
  intro w hw
  by_cases hs : (D.fm u).seenP w = true
  · have hR : Rat0 D u := rational_level_zero_of_integral w hw hs h4
    have hg : ∀ v ∈ (VV D u w).toList, (Sram D u w).map (gR hR w v) ≤ Sram D u w :=
      fun v hv => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw (Finset.mem_toList.mp hv)).1
    obtain ⟨hG, hGl⟩ := len_list_le (Sram D u w) (gR hR w) (VV D u w).toList hg
    obtain ⟨hP, hPl⟩ := len_pow_le (Sram D u w) (GR hR w (VV D u w).toList) hG D.R.m
    rw [Nlam_eq hS hR w]
    refine ⟨hP, ?_⟩
    have H : ∀ v : {v // v ∈ VV D u w}, ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℚ) +
            (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℚ)) / (D.R.k : ℚ)) ∧
        Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v.1)).comap (Sram D u w).subtype) ≤
          ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) :=
      fun v => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw v.2).2
    choose nn hnq hnl using H
    have hsum : Module.length (Ow D w) (Sram D u w ⧸
        ((Sram D u w).map (GR hR w (VV D u w).toList ^ D.R.m)).comap (Sram D u w).subtype) ≤
        ((D.R.m * ∑ v ∈ (VV D u w).attach, (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℕ∞) := by
      refine le_trans hPl ?_
      push_cast
      rw [nsmul_eq_mul]
      refine mul_le_mul_right (le_trans hGl ?_) _
      rw [Finset.sum_map_toList, ← Finset.sum_attach]
      exact Finset.sum_le_sum (fun v _ => by exact_mod_cast hnl v)
    obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hsum
    refine ⟨n, hn, ?_⟩
    have hk : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
    have he : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
    have hterm : ∀ v : {v // v ∈ VV D u w},
        ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (D.duS u * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
            (D.fm u).bTop ((D.fm u).tauOf w v.1))) := by
      intro v
      have ht := (mem_VV v.2).2
      have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v.1) := hS.2.2 _ ht
      have hbR : (0 : ℝ) ≤ ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := by exact_mod_cast hb
      have hN1 := twist_le (u := u) ht
      have hq : ((nn v : ℕ) : ℝ) = (D.what₂.places.ramIdx w : ℝ) * ((D.duS u : ℝ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hnq v)
        push_cast at this; exact this
      have hk1 : ((D.R.k - 1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Nat.sub_le _ _
      push_cast
      rw [hq, mul_div_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ he
      have e1 : (D.duS u : ℝ) * (((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) ≤
          (D.duS u : ℝ) * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1)) :=
        mul_le_mul_of_nonneg_left hN1 hd
      have e2 : ((D.R.k - 1 : ℕ) : ℝ) * (D.duS u : ℝ) ≤ (D.duS u : ℝ) * (D.R.k : ℝ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk1 hd
      have e3 : 0 ≤ (D.duS u : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := mul_nonneg hd hbR
      nlinarith
    calc (n : ℝ) ≤ ((D.R.m * ∑ v ∈ (VV D u w).attach,
            (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach,
            ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach, ((D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v.1)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hterm v)) (Nat.cast_nonneg _)
      _ = _ := by
          rw [Finset.sum_attach (VV D u w) (fun v => (D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v)))), ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  · have hs' : (D.fm u).seenP w = false := by simpa using hs
    have hVV : VV D u w = ∅ := by simp [LT.VVT, hs']
    have hN : Nlam D u w = Sram D u w := by
      have := imgL_eq_map (u := u) w ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (Uprod D u 0 w) ^ D.R.m) LinearMap.id
        (fun x => by simp [LT.expT, LT.Uprod, LT.VVT, hs']) (Sram D u w)
      rw [Submodule.map_id] at this
      exact this
    rw [hN, hVV]
    refine ⟨le_rfl, 0, ?_, by simp⟩
    unfold len
    rw [Submodule.comap_subtype_self]
    simp

theorem congruence_no_kernel_family_minimal
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ HeckeRamifiedLevelZero D u ∧ SecondBranchInclusionLength D u) : CongruenceLatticeLengthBoundFamily := fun D u hF hS hA =>
  have h' := h D u hF hS hA
  congruence_no_kernel_minimal hS h'.2.2 h'.1 h'.2.1

end Min

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
