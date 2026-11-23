import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.TransportCong

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem inModL_of_inMod_embA : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hA b bd y hy
  obtain ⟨h1, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA
  have hadd : ∀ x x', embA X wt ιA (x + x') = embA X wt ιA x + embA X wt ιA x' := by
    intro x x'; simp only [embA, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : D.host.E ⊗[D.host.F] Ad D.host.F) x,
      embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
    intro c x; simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hzero : embA X wt ιA 0 = 0 := by simp [embA]
  have hsub : ∀ x x', embA X wt ιA (x - x') = embA X wt ιA x - embA X wt ιA x' := by
    intro x x'
    have := hadd (x - x') x'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hS : (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) =
      embA X wt ιA '' (Set.range b ∪ Set.range bd) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]; rfl
  have hspan : ∀ s ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (embA X wt ιA '' (Set.range b ∪ Set.range bd)),
      ∃ s' ∈ Submodule.span (OAd D.host.F D.host.E) (Set.range b ∪ Set.range bd), embA X wt ιA s' = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact ⟨t, Submodule.subset_span ht, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, hzero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      obtain ⟨s2, hs2, rfl⟩ := ihx'
      exact ⟨s1 + s2, Submodule.add_mem _ hs1 hs2, hadd _ _⟩
    | smul a x _ ihx =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      have ha : ιA (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hA.2 a).1 a.2
      refine ⟨(⟨_, ha⟩ : OAd D.host.F D.host.E) • s1, Submodule.smul_mem _ _ hs1, ?_⟩
      rw [Subring.smul_def, hsmul, RingEquiv.symm_apply_apply, Subring.smul_def]
  have hmL : ∀ w ∈ mL X.B.I X.B.g, ∃ x ∈ X.B.I.Lf,
      w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨x', hx', rfl⟩ := hx; exact ⟨x', hx', rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, (smul_zero _).symm⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      obtain ⟨a2, h2, rfl⟩ := ihx'
      exact ⟨a1 + a2, Submodule.add_mem _ h1 h2, (smul_add _ _ _).symm⟩
    | smul a x _ ihx =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      refine ⟨a • a1, Submodule.smul_mem _ _ h1, ?_⟩
      simp only [Subring.smul_def, smul_smul, mul_comm]
  unfold InMod at hy
  rw [hS] at hy
  obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s', hs', rfl⟩ := hspan s hs
  obtain ⟨x, hx, rfl⟩ := hmL w hw
  rw [X.g_eq] at hsw
  rcases Nat.eq_zero_or_pos (D.host.g 0 * D.host.g 1) with h0 | hpos
  · refine ⟨s', hs', 0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, add_zero]
    apply hinj
    rw [← hsw, h0, Nat.cast_zero, zero_smul, add_zero]
  · have hu : IsUnit (((D.host.g 0 * D.host.g 1 : ℕ)) : D.host.E ⊗[D.host.F] Ad D.host.F) := by
      rw [← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')).map _
    obtain ⟨c, hc⟩ := hu
    refine ⟨s', hs', ((c⁻¹ : (D.host.E ⊗[D.host.F] Ad D.host.F)ˣ) : D.host.E ⊗[D.host.F] Ad D.host.F) • (y - s'), ?_, ?_⟩
    · rw [h1, hsmul, hsub, ← hsw, add_sub_cancel_left, smul_smul, ← map_natCast ιA.symm, ← hc,
        ← map_mul, Units.inv_mul, map_one, one_smul]
      exact hx
    · rw [smul_smul, ← hc, Units.mul_inv, one_smul, add_sub_cancel]

end GlobalTheory.St.G.TransportCong
