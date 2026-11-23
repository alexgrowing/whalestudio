import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.SharpRestriction.GlobalTheoremInputs

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem served_prime_lattices (Gi : Inst D L) (K : Consts) (C bo : ℝ) (h : LinkG_at Gi K C bo) : Formalism.MainNotions.LocalQuadraticParts.adm18 Gi K :=
  ⟨h.1, h.2.1⟩

theorem family_served_prime_lattices {eps : ℝ} (Fm : FamP eps) (h : LinkG Fm) : Formalism.MainNotions.LocalQuadraticParts.G1Family Fm := by
  obtain ⟨C, x0, δ, _, H⟩ := h
  exact ⟨x0, fun x hx i => served_prime_lattices _ _ C _ (H x hx i)⟩

theorem served_orbits_band_bad_probability (Gi : Inst D L) (K : Consts) (Cb : ℝ) (h33 : Formalism.MainNotions.CornerGLContinuity.OrdersLargePrimeBound D L K)
    (h32 : Formalism.MainNotions.CornerGLContinuity.BadPrimeBound D L Gi Cb) : Formalism.MainNotions.LocalQuadraticParts.adm20 Gi K Cb :=
  ⟨served_orbits_in_set Gi K _ _, h33.2.2.2.1, h32⟩

theorem family_served_orbits_band {eps : ℝ} (Fm : FamP eps) (h33 : Formalism.MainNotions.CornerGLContinuity.FamilyOrdersLargePrimeBoundConstant Fm) (h32 : Formalism.MainNotions.CornerGLContinuity.FamilyBadPrimeBound Fm) :
    Formalism.MainNotions.LocalQuadraticParts.G3BoundFamily Fm := by
  obtain ⟨x0, h0⟩ := h33
  obtain ⟨Cb, _, x1, h1⟩ := h32
  exact ⟨Cb, max x0 x1, fun x hx i => served_orbits_band_bad_probability _ _ Cb (h0 x (le_trans (le_max_left _ _) hx) i)
    (h1 x (le_trans (le_max_right _ _) hx) i)⟩

theorem family_mean_shares_windows {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx) : Formalism.MainNotions.LocalQuadraticParts.FontaineFormalPropertiesFamily Fm := by
  obtain ⟨C, δ, _, x0, H⟩ := h
  exact ⟨x0, fun x hx i => (H x hx i).2.1⟩

def ExcSplit (L : SizeData₂ D) : Prop :=
  ∀ u p, p.Prime → Formalism.MainNotions.LocalQuadraticParts.Exc L u p → p = D.host.d ∨ ¬ InertK D p

theorem sizes_depths_thresholds (Gi : Inst D L) (K : Consts) (C bo : ℝ) (h1 : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C)
    (h2 : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C bo) (h3 : ExcSplit L) : Formalism.MainNotions.LocalQuadraticParts.HerrCocycleExtensionClass Gi K C bo :=
  ⟨h1, h2, h3⟩

theorem sc_a_pos (s : Scale) : 1 < s.a := by
  have hx := s.one_lt_alt
  have hb : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  unfold Scale.a
  nlinarith

theorem tau_size_bound_mono (Gi : Inst D L) (K : Consts) {C C' : ℝ} (hC : C ≤ C')
    (h : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C) : Formalism.MainNotions.CornerGLContinuity.CutSizes D L Gi K C' := by
  have ha : 0 < L.sc.a := lt_trans one_pos (sc_a_pos L.sc)
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  refine ⟨fun t0 ht => ?_, fun hV => ?_⟩
  · have hn : 0 ≤ (Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ) := by positivity
    have e : ∀ c : ℝ, c * (Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ) = c * ((Nv Gi p t0 : ℝ) * L.sc.a / (p : ℝ)) :=
      fun c => by ring
    have hm := mul_le_mul_of_nonneg_right hC hn
    have h1' := h1 t0 ht
    rw [e C']
    rw [e C] at h1'
    exact ⟨le_trans h1'.1 hm, le_trans h1'.2 hm⟩
  · have hl : 0 ≤ Real.logb p L.sc.a := by
      rcases Nat.lt_or_ge 1 p with h1p | h1p
      · exact Real.logb_nonneg (by exact_mod_cast h1p) (sc_a_pos L.sc).le
      · interval_cases p <;> simp [Real.logb]
    have hn : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a := by positivity
    have e : ∀ c : ℝ, c * D.R.f * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a =
        c * ((D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) := fun c => by ring
    rw [e C']
    have := h2 hV
    rw [e C] at this
    exact le_trans this (mul_le_mul_of_nonneg_right hC hn)

theorem tau_sum_bound_mono {C C' bo : ℝ} (hC : C ≤ C') (h : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C bo) : Formalism.MainNotions.CornerGLContinuity.WeightSumBound D L C' bo := by
  have ha : 0 < L.sc.a := lt_trans one_pos (sc_a_pos L.sc)
  have hX : 0 ≤ Real.log L.sc.X' := by
    unfold Scale.X'
    rw [Real.log_exp]
    exact Real.rpow_nonneg (lt_trans one_pos L.sc.one_lt_alt).le _
  have hn : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' := by positivity
  have e : ∀ c : ℝ, c * D.R.m * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' =
      c * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X') := fun c => by ring
  unfold Formalism.MainNotions.CornerGLContinuity.WeightSumBound at h ⊢
  rw [e C']
  rw [e C] at h
  linarith [mul_le_mul_of_nonneg_right hC hn]

theorem family_sizes_depths_thresholds {eps : ℝ} (Fm : FamP eps) (h1 : Formalism.MainNotions.CornerGLContinuity.FamilyCutSizes Fm) (h2 : Formalism.MainNotions.CornerGLContinuity.FamilyWeightSumBound Fm)
    (h3 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ExcSplit (Fm.L x i)) : Formalism.MainNotions.LocalQuadraticParts.AddedTermFamily Fm := by
  obtain ⟨C1, x1, H1⟩ := h1
  obtain ⟨C2, x2, δ, hδ, H2⟩ := h2
  obtain ⟨x3, H3⟩ := h3
  refine ⟨max C1 C2, max x1 (max x2 x3), δ, hδ, fun x hx i => ?_⟩
  have a1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have a2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have a3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  exact sizes_depths_thresholds _ _ _ _ (tau_size_bound_mono _ _ (le_max_left _ _) (H1 x a1 i))
    (tau_sum_bound_mono (le_max_right _ _) (H2 x a2 i)) (H3 x a3 i)

end Formalism.MainNotions.J

end
