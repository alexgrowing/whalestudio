import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def LevelPrimeBasicClauses (D : D7) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax

theorem levelPrimeClauses_of_second (D : D7) (h : ∀ u, product_first_zeroth_parts.Conclusion2 D u) : LevelPrimeBasicClauses D := by
  intro u
  obtain ⟨h1, h2, h3, -⟩ := h u
  obtain ⟨s1, s2, -⟩ := D.ram_slopes u
  refine ⟨?_, ?_, ?_⟩
  · have h1' := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h1'
    rw [h1']
    ring
  · rw [show (LocalQuadraticParts.MuH D u).mu = (D.fm u).ramLat.mu from s1]
    exact h2
  · rw [show (LocalQuadraticParts.MuH D u).muMax = (D.fm u).ramLat.muMax from s2]
    exact h3

theorem sum_lwP_e_le (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w ∈ S, D.what₂.places.resChar w = p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p := by
  classical
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => mul_nonneg (lw_nonneg v) (Nat.cast_nonneg _))

def LenAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T →
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) =
      product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w)

def LocSpan (D : D7) : Prop :=
  ∀ u w, ∀ y ∈ (D.fm u).S 0 w, InLoc (D.plEq w) ((D.fm u).lat 0).L y

def LevelPrimeSizeBounds (D : D7) (L : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ u w, product_first_zeroth_parts.OverT D u w → ∑ v ∈ product_first_zeroth_parts.VV D u w,
      ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤
    C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b')

theorem levelPrime_summary_of_fifth (D : D7) (L : SizeData₂ D) (C C1 : ℝ) (h2 : ∀ u, product_first_zeroth_parts.Conclusion2 D u)
    (h5 : ∀ u, product_first_zeroth_parts.Conclusion5 D u C) (hNu : DV.NuDef D L) (hAtT : NuAtTDef D L) (hLoc : LocSpan D)
    (hLen : LenAtT D L) (hS : LevelPrimeSizeBounds D L C1)
    (hSet : ∀ u, product_first_zeroth_parts.HidaSetting D u) (hC1 : 0 ≤ C1) : LocalQuadraticParts.adm26 L (4 * C1) := by
  classical
  intro u
  obtain ⟨c1, c2, c3⟩ := levelPrimeClauses_of_second D h2 u
  refine ⟨c1, c2, c3, ?_, ?_⟩
  · intro w hw x hx
    have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
    have h2 : D.nuIn u x ∈ product_first_zeroth_parts.Nlam D u w := (hAtT u w hw x).mp h1
    have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := ((h5 u w hw).1 h2).1
    obtain ⟨s, hs, hsx⟩ := hLoc u w _ h3
    refine ⟨s, hs, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    show (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · intro F hFT
    have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    have ha : 0 < L.sc.a := mul_pos hx0 (Real.exp_pos _)
    have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ D.duS u := Nat.cast_nonneg _
    have hTT : (0 : ℝ) ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
    set B : ℝ := C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * (2 * (D.R.m * D.duS u * B)) := by
      intro w hw
      have hwT : D.what₂.places.resChar w = (D.mem u).A.T := hFT w hw
      obtain ⟨-, -, n, hn, hle⟩ := h5 u w hwT
      have hl := hNu.2.2 u w n (by rw [hLen u w hwT, hn])
      have hlw := logWeight_nonneg w
      have he : (0 : ℝ) ≤ D.what₂.places.ramIdx w := Nat.cast_nonneg _
      have hSw := hS u w hwT
      have h1 : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B) :=
        le_trans hle (by gcongr)
      unfold SizeData₂.sz
      calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ))
          = 2 * SizeData₂.lwP w * (n : ℝ) := by rw [hl]; ring
        _ ≤ 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B)) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        Real.log ((D.mem u).A.T : ℝ) * (2 * (D.R.m * D.duS u * B)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_lwP_e_le D _ (D.mem u).A.T_prime F hFT) (by positivity)

    have hN1 : 1 ≤ D.R.N D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.N; omega
    have hTf : 2 * D.R.f + 1 < (D.mem u).A.T := by
      have h := (hSet u).1
      have : 2 * D.R.f ≤ 2 * D.R.f * D.R.N D.R.m := Nat.le_mul_of_pos_right _ hN1
      omega
    have hTfR : 2 * (D.R.f : ℝ) + 1 < (D.mem u).A.T := by exact_mod_cast hTf
    have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hT1 : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
    have hT2 : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hr : (1 / 2 : ℝ) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := by
      have hb := one_add_mul_le_pow (a := -(1 / (((D.mem u).A.T : ℝ) - 1))) (by
        have : 1 / (((D.mem u).A.T : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hT1]; linarith
        linarith) D.R.f
      have h3 : (D.R.f : ℝ) * (1 / (((D.mem u).A.T : ℝ) - 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hT1]; linarith
      have h4 : (1 + -(1 / (((D.mem u).A.T : ℝ) - 1))) = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by ring
      rw [h4] at hb
      linarith
    have hgoal : (4 * C1) * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') *
        Real.log ((D.mem u).A.T : ℝ) = 4 * (D.R.m * B * Real.log ((D.mem u).A.T : ℝ)) := by
      rw [hB]; ring
    rw [hgoal]
    rcases eq_or_lt_of_le hd with h0 | h0
    · rw [c1, ← h0, mul_zero, div_zero]; positivity
    · have hdu : 0 < ((D.mem u).A.du : ℝ) := by rw [c1]; positivity
      rw [div_le_iff₀ hdu]
      refine le_trans hsum ?_
      rw [c1]
      have : (D.duS u : ℝ) * (1 / 2) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) := by
        rw [mul_comm]; gcongr
      have hP : 0 ≤ D.R.m * B * Real.log ((D.mem u).A.T : ℝ) := by positivity
      nlinarith

theorem family_levelPrime_summary {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧ LocSpan (Fm.D x i) ∧
      LenAtT (Fm.D x i) (Fm.L x i) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hx0⟩ := hE
  refine ⟨4 * C1, max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have hxx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx
    linarith
  obtain ⟨h2, h5, hLoc, hLen, hS, hSet⟩ := hx0 x hxx0 i
  exact levelPrime_summary_of_fifth (Fm.D x i) (Fm.L x i) C C1 h2 h5 (Fm.nuDef x hx1 i) (Fm.ex x hx1 i).lat.atT hLoc hLen hS
    hSet hC1

end Formalism.MainNotions.J
