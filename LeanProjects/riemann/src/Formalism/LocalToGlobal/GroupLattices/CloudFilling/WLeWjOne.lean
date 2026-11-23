import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero

noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

theorem wG_idx (R : Ranks) (e : Fin R.m → ℚ) (b j : ℕ) (hb : b < R.m) (hj : j - 1 < R.m) (h : b = j - 1) (h1 : 1 ≤ j) :
    wG R (e ⟨b, hb⟩) (b + 1) = wG R (e ⟨j - 1, hj⟩) j := by
  subst h
  rw [Nat.sub_add_cancel h1]

theorem wRec_eq (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    ((wRec D u g j : ℤ) : ℝ) = wj D j (D.eTau.symm g) - Formalism.MainNotions.G.kaJ D j := by
  have hj' := Finset.mem_Icc.1 hj
  have hjm : j - 1 < D.R.m := by omega
  have h := (D.fm u).lam_eq D.R.m le_rfl (D.eTau.symm g)
    ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩
  rw [dif_neg (by show ¬ D.R.k + (min j D.R.m - 1) * (D.R.t + 1) < D.R.k; omega)] at h
  have hb : (D.R.k + (min j D.R.m - 1) * (D.R.t + 1) - D.R.k) / (D.R.t + 1) = j - 1 := by
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _), min_eq_left hj'.2]
  have h' : ((((D.fm u).lam D.R.m (D.eTau.symm g)).w
      ⟨D.R.k + (min j D.R.m - 1) * (D.R.t + 1), blkIdx_lt D.R j⟩ : ℤ) : ℚ) =
      -wG D.R ((D.hcW u (D.eTau.symm g)).e ⟨j - 1, hjm⟩) j := by
    rw [h]
    exact congrArg Neg.neg (wG_idx D.R _ _ j _ hjm hb hj'.1)
  rw [D.hcW_e] at h'
  have h'' := congrArg (fun q : ℚ => (q : ℝ)) h'
  simp only [wG] at h''
  push_cast at h''
  unfold wRec wj Formalism.MainNotions.G.kaJ
  rw [dif_pos hjm]
  push_cast
  rw [h'']
  ring

theorem lamRec_real (D : D7) (u : D.what₂.Word) (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)) (hi : i.1 < D.R.k) :
    ((lamRec D u g i : ℤ) : ℝ) =
      (((D.hcW u (D.eTau.symm g)).u ⟨i.1, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ)) := by
  have h := (D.fm u).lam_eq 0 (Nat.zero_le _) (D.eTau.symm g) ⟨i.1, by simp only [Ranks.N]; omega⟩
  rw [dif_pos hi] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [hcToWeightQ, rhoVec] at h'
  push_cast at h'
  exact h'

theorem lamRec_top {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (g : D.R.Psi) (t : D.host.TT)
    (ht : (g : D.R.GG) = D.R.tau1 t) :
    lamRec D u g 0 = L.aT t ∧ lamRec D u g (Fin.last _) = -L.bT t := by
  have hk := k_pred D.R
  have hk0 : 0 < D.R.k := by omega
  have hkR : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have tu := L.top_u (D.eTau.symm g) t hk0 (by rw [Equiv.apply_symm_apply]; exact ht)
  constructor
  · have h := lamRec_real D u g 0 (by simpa using hk0)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(0 : Fin (D.R.k - 1 + 1)).1, by simpa using hk0⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext (by simp)
    rw [e, D.hcW_first u _ hk0, tu.1]
    simp
  · have h := lamRec_real D u g (Fin.last _) (by simp only [Fin.val_last]; omega)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(Fin.last (D.R.k - 1)).1, by simp only [Fin.val_last]; omega⟩ : Fin D.R.k) =
        ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_last])
    rw [e, D.hcW_last u _ hk0, tu.2]
    simp only [Fin.val_last]
    rw [hkR]
    push_cast
    ring

def cRec {D : D7} (L : SizeData₂ D) : ℕ := ⌊Formalism.MainNotions.G.cG L⌋₊

theorem cG_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.G.cG L := by
  unfold Formalism.MainNotions.G.cG
  linarith [L.Sc_pos]

theorem cRec_le {D : D7} (L : SizeData₂ D) : (cRec L : ℝ) ≤ Formalism.MainNotions.G.cG L := Nat.floor_le (cG_nonneg L)

theorem lt_cRec {D : D7} (L : SizeData₂ D) : 4 * L.Sc - 1 < (cRec L : ℝ) := by
  have := Nat.lt_floor_add_one (Formalism.MainNotions.G.cG L)
  unfold cRec
  unfold Formalism.MainNotions.G.cG at this ⊢
  linarith

theorem ktl_le_Del {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    (D.R.k : ℝ) + D.R.t + 1 ≤ (D.s.Del : ℝ) := by
  have h := P.Del_ge.2.2.2
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm
  have hN : (D.R.k : ℝ) + D.R.t + 1 ≤ (D.R.N D.R.m : ℝ) := by
    simp only [Ranks.N]
    push_cast
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) + 1 := by positivity
    nlinarith
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem five_le_k (R : Ranks) : (5 : ℝ) ≤ (R.k : ℝ) := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  exact_mod_cast (by omega : 5 ≤ R.k)

theorem ktl_le_Sc {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : 20 * ((D.R.k : ℝ) + D.R.t + 1) ≤ L.Sc := by
  have h1 := ktl_le_Del P
  have h2 := five_le_k D.R
  have h3 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  rw [L.Sc_eq]
  nlinarith

theorem w''_le_wj_one {D : D7} (L : SizeData₂ D) (τ : D.what₂.Tau) : L.sc.w'' D.R.n ≤ wj D 1 τ := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hle := Formalism.MainNotions.Inhab.scale_w''_le L.sc D.R.n (Formalism.MainNotions.Inhab.ranks_one_le_n D.R)
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
    have h1 := (L.win_top 1 le_rfl hm τ ⟨t, ht⟩ hte.symm).1
    have h2 := L.bT_ge ⟨t, ht⟩
    have h3 := Formalism.MainNotions.Inhab.scale_b'_nonneg L.sc
    linarith [hle.1]
  · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have h1 := (L.win_thick 1 le_rfl hm τ hth).1
      linarith [hle.2]
    · exact (L.win_thin 1 le_rfl hm τ ⟨(D.eTau τ).2, htop, hth⟩).1

theorem cloudBound {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (u : D.what₂.Word) : CloudBound D u (cRec L) := by
  have hk := k_pred D.R
  have hk5 := five_le_k D.R
  have hk5n : 5 ≤ D.R.k := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    omega
  have hS := ktl_le_Sc P
  have hc := lt_cRec L
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hmid : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 →
      |lamRec D u g i| ≤ (cRec L : ℤ) := by
    intro g i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := lamRec_real D u g i hi
    have cl := L.cloud_u u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
      rw [h, abs_le]
      constructor <;> linarith [cl.1, cl.2]
    exact_mod_cast h2
  refine ⟨fun g _ i h0 h1 => hmid g i h0 h1, fun g hg i => ?_, fun g => ?_⟩
  · have hg' : (D.eTau (D.eTau.symm g) : D.R.GG) ∉ D.host.topPlaces := by rwa [Equiv.apply_symm_apply]
    have hk0 : 0 < D.R.k := by omega
    by_cases h0 : i.val = 0
    · have hi : i.1 < D.R.k := by omega
      have h := lamRec_real D u g i hi
      have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext h0
      rw [e, D.hcW_first u _ hk0, h0] at h
      have g1 := (L.cloud_gap (D.eTau.symm g) (by omega) hg').1
      have g2 := P.cloud_place_bound (D.eTau.symm g) (by omega) hg'
      have g3 := L.cloud_v (D.eTau.symm g) ⟨0, by omega⟩
      push_cast at g1 g2
      have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
        rw [h, abs_le]
        push_cast
        constructor <;> linarith [g3.1, g3.2]
      exact_mod_cast h2
    · by_cases h1 : i.val < D.R.k - 1
      · exact hmid g i (Nat.pos_of_ne_zero h0) h1
      · have hi1 : i.val = D.R.k - 1 := by have := i.2; omega
        have hi : i.1 < D.R.k := by omega
        have h := lamRec_real D u g i hi
        have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi1
        have hkR : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [e, D.hcW_last u _ hk0, P.uk_extreme (D.eTau.symm g) (by omega) hg', hi1, hkR] at h
        have g3 := L.cloud_v (D.eTau.symm g) ⟨D.R.k - 2, by omega⟩
        push_cast at h
        have h2 : |((lamRec D u g i : ℤ) : ℝ)| ≤ (cRec L : ℝ) := by
          rw [h, abs_le]
          constructor <;> linarith [g3.1, g3.2]
        exact_mod_cast h2
  · have h1 : (1 : ℕ) ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
    have hw := wRec_eq D u g 1 h1
    have hw'' := w''_le_wj_one L (D.eTau.symm g)
    have hkS := P.kS_le
    have hSc := L.Sc_pos
    have hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2 := by
      unfold Formalism.MainNotions.G.kaJ
      push_cast
      ring
    have hcle := cRec_le L
    unfold Formalism.MainNotions.G.cG at hcle
    have h5 : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
    have h2 : ((cRec L : ℕ) : ℝ) ≤ ((wRec D u g 1 : ℤ) : ℝ) := by
      rw [hw, hka]
      linarith
    exact_mod_cast h2

end Formalism.L2.G
