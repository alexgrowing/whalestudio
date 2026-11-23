import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open GlobalTheory.CuspRep.Generic

namespace PositivityTheory.jumpWindows.WhittakerFunctional

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem norm_avg_le (Γ : AddSubgroup G) (Φ : G → ℂ) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x, ‖Φ x‖ ≤ C) :
    ‖avg Γ Φ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with h
  · have h1 := h.choose_spec.2.2
    have hs : h.choose.1 h.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    have := norm_setIntegral_le_of_norm_le_const hs (f := Φ) (fun x _ => hC x)
    simpa [Measure.real, h1] using this
  · simpa using h0

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem norm_colT_le (hψ : StdPsi ψ) (k : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖colT ψ k f g‖ ≤ C := by
  refine norm_avg_le _ _ h0 fun x => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact hf _

theorem norm_whit_le (hψ : StdPsi ψ) (m : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖whit ψ m f g‖ ≤ C := by
  induction m generalizing f g with
  | zero => exact hf g
  | succ m ih =>
    rw [whit_succ]
    exact ih (fun g => norm_colT_le hψ (m + 1) h0 hf g) g

theorem good_add {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') :
    Good ψ m (fun g => f g + f' g) where
  cont := hf.cont.add hf'.cont
  left γ hγ g := by simp only [hf.left γ hγ g, hf'.left γ hγ g]
  law k hk y g := by simp only [hf.law k hk y g, hf'.law k hk y g, mul_add]
  van r hr hrm g := by
    have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _
      (per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g)
      (per_blk hf'.cont (fun c g => hf'.left _ (isMir_blkU c) g) g)
    rw [this, hf.van r hr hrm g, hf'.van r hr hrm g, add_zero]

theorem good_smul (c : ℂ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) : Good ψ m (fun g => c * f g) where
  cont := continuous_const.mul hf.cont
  left γ hγ g := by simp only [hf.left γ hγ g]
  law k hk y g := by simp only [hf.law k hk y g]; ring
  van r hr hrm g := by
    show avg _ (fun x => c * f (blkU x * g)) = 0
    rw [avg_const_mul, hf.van r hr hrm g, mul_zero]

theorem good_zero (m : ℕ) : Good ψ m (fun _ : GA E a => (0 : ℂ)) where
  cont := continuous_const
  left _ _ _ := rfl
  law _ _ _ _ := by simp
  van r _ _ g := by
    have := avg_const_mul (ratV E (UnipotentBlockColumnIndex a r m)) 0 (fun _ => 0)
    simpa using this

theorem good_rt {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (h : GA E a) : Good ψ m (fun x => f (x * h)) where
  cont := hf.cont.comp (continuous_id.mul continuous_const)
  left γ hγ g := by simp only [mul_assoc, hf.left γ hγ (g * h)]
  law k hk y g := by simp only [mul_assoc, hf.law k hk y (g * h)]
  van r hr hrm g := by
    simp only [mul_assoc]
    exact hf.van r hr hrm (g * h)

theorem dot_eLast (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

variable (E a) in

def Yg (hψ : StdPsi ψ) : Submodule ℂ (XB E a) where
  carrier := {φ | Good ψ (a - 1) φ}
  add_mem' h h' := good_add h h'
  zero_mem' := good_zero (a - 1)
  smul_mem' c _ h := good_smul c h

def whL (hψ : StdPsi ψ) (g : GA E a) : Yg E a hψ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => whit ψ (a - 1) (φ.1 : GA E a → ℂ) g
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) (by omega) φ.2 φ'.2) g
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c (φ.1 : GA E a → ℂ)) g } 1
    fun φ => by
      rw [one_mul]
      exact norm_whit_le hψ _ (norm_nonneg _) (fun g => φ.1.norm_coe_le_norm g) g

end PositivityTheory.jumpWindows.WhittakerFunctional

namespace PositivityTheory.jumpWindows

theorem local_group_averaging_tensor : G5 := by
  intro E _ _ _ a ψ hψ
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  refine ⟨fun g => ?_, fun φ g h => ?_, fun φ h hφ => ?_, fun φ hφ => ⟨?_, fun hne => ?_, fun k hk y g => ?_⟩⟩
  · obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (WhittakerFunctional.Yg E a hψ) (WhittakerFunctional.whL hψ g)
    refine ⟨Λ, fun φ hφ => ?_⟩
    have := hΛ ⟨φ, hφ⟩
    rw [WhittakerFunctional.whL, LinearMap.mkContinuous_apply] at this
    exact this
  · exact whit_rt (a - 1) φ h g
  · exact WhittakerFunctional.good_rt hφ h
  · exact (whit_good hψ (a - 1) h0 hφ).1.cont
  · have hf : (φ : GA E a → ℂ) ≠ 0 := fun h => hne (DFunLike.coe_injective (by simpa using h))
    obtain ⟨g, hg⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 hφ).2 hf)
    exact ⟨g, hg⟩
  · rw [← WhittakerFunctional.dot_eLast]
    exact (whit_good hψ (a - 1) h0 hφ).1.law k hk y g

end PositivityTheory.jumpWindows

end
