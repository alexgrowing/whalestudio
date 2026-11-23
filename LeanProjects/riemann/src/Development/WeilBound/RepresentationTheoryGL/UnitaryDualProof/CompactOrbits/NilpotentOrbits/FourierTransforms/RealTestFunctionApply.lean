import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceNilpotentConeProjection

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

def Dl : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (d Z) → k) where
  toFun := D Z
  map_add' := D_add Z
  map_smul' := D_smul Z

abbrev TT : Type := ↥(LinearMap.ker (Dl Z)) × (Fin n → k)

theorem continuous_E : Continuous (E Z) := by
  have e : E Z = fun u => ∑ j, u j • ee Z j := funext (E_apply Z)
  rw [e]
  exact continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const

theorem continuous_D : Continuous (D Z) :=
  continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_trace

theorem continuous_Pr : Continuous (Pr Z) :=
  (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D Z))

variable {Z}
variable (hZ : CR Z) (h : Hyp Z)

def Hb : Sp k n ≃ₜ TT Z × (Fin (d Z) → k) where
  toFun p := ((⟨p.1 - Pr Z p.1, by show D Z _ = 0; exact D_sub_Pr hZ h _⟩, p.2), D Z p.1)
  invFun q := (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := by
    ext1
    · show p.1 - Pr Z p.1 + E Z ((G Z)⁻¹ *ᵥ D Z p.1) = p.1
      rw [← Pr, sub_add_cancel]
    · rfl
  right_inv q := by
    obtain ⟨⟨⟨y, hy⟩, v⟩, w⟩ := q
    have hy' : D Z y = 0 := hy
    have hPy : Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = E Z ((G Z)⁻¹ *ᵥ w) := by
      rw [Pr_add, Pr_of_D hZ h hy', Pr_E hZ h, zero_add]
    have hDx : D Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = w := by
      rw [D_add, hy', zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
    refine Prod.ext (Prod.ext (Subtype.ext ?_) rfl) hDx
    show y + E Z ((G Z)⁻¹ *ᵥ w) - Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = y
    rw [hPy, add_sub_cancel_right]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
      ((continuous_D Z).comp continuous_fst)
    exact continuous_fst.sub ((continuous_Pr Z).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))

def Gm : (Fin (d Z) → k) ≃ₜ (Fin (d Z) → k) where
  toFun u := G Z *ᵥ u
  invFun u := (G Z)⁻¹ *ᵥ u
  left_inv u := by
    show (G Z)⁻¹ *ᵥ (G Z *ᵥ u) = u
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  right_inv u := by
    show G Z *ᵥ ((G Z)⁻¹ *ᵥ u) = u
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT Z × (Fin (d Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT Z)).prodCongr (Gm hZ h)).trans (Hb hZ h).symm

theorem real_test_function_apply (q : TT Z × (Fin (d Z) → k)) : F1 hZ h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ (G Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
