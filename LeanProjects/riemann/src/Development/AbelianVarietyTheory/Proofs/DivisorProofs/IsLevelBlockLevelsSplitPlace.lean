import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_dgM_inl {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw a w => dgMat h x.val (1 : GLw b w).val
    exact (Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  · have : (fun x : GLw a w => (((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h (x⁻¹).val ((1 : GLw b w)⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks Units.continuous_coe_inv continuous_const continuous_const
      continuous_const).matrix_reindex _ _

theorem continuous_dgM_inr {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw b w => dgMat h (1 : GLw a w).val x.val
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_val).matrix_reindex _ _
  · have : (fun x : GLw b w => (((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h ((1 : GLw a w)⁻¹).val (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_coe_inv).matrix_reindex _ _

theorem continuous_det_GLw (m : ℕ) (w : Pl E) :
    Continuous (GeneralLinearGroup.det : GLw m w → (w.adicCompletion E)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw m w => (x.val).det
    exact Units.continuous_val.matrix_det
  · have : (fun x : GLw m w => ((GeneralLinearGroup.det x)⁻¹ : (w.adicCompletion E)ˣ).val) =
        fun x => ((x⁻¹).val).det := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem isOpen_detKer (m : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : IsOpen {x | μ x = 1}) :
    IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw m w)) : Set (GLw m w)) :=
  hμ.preimage (continuous_det_GLw m w)

theorem thL_split (m : ℕ) (w : Pl E) (hw : IsSplitAt w) : thL m w = MonoidHom.id _ := by
  rw [thL, if_pos hw]

end GlobalTheory.BCT.CtLevel

theorem GlobalTheory.BCT.CtLevel.isLevel_lev_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (lev₂ h w N μ) := by
  intro E _ _ _ a b n h w N μ hw hN hμ
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.inter
      (hN.preimage (continuous_dgM_inl h w))).inter (isOpen_detKer a w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split a w hw]
    exact hk
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1.inter
      (hN.preimage (continuous_dgM_inr h w))).inter (isOpen_detKer b w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split b w hw]
    exact hk
