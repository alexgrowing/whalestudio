import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.DistribHaarCharAdU

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

theorem tau_sum (x : Matrix (Fin n) (Fin n) k) : τ x = ∑ i, ∑ j, x i j * τ (Matrix.single i j 1) := by
  have e : ∀ i j, Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : k) := fun i j => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [e, map_sum, map_smul, smul_eq_mul]

theorem continuous_tau : Continuous τ := by
  rw [show (⇑τ) = fun x => ∑ i, ∑ j, x i j * τ (Matrix.single i j 1) from funext (tau_sum τ)]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

def Dl : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (dd Z) → k) where
  toFun := D τ Z
  map_add' := D_add τ Z
  map_smul' := D_smul τ Z

abbrev TT : Type := ↥(LinearMap.ker (Dl τ Z)) × (Fin n → k)

theorem continuous_E : Continuous (E Z) := by
  have e : E Z = fun u => ∑ j, u j • ee Z j := funext (E_apply Z)
  rw [e]
  exact continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const

theorem continuous_D : Continuous (D τ Z) :=
  continuous_pi fun j => (continuous_tau τ).comp (continuous_const.matrix_mul continuous_id)

theorem continuous_Pr : Continuous (Pr τ Z) :=
  (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D τ Z))

variable {τ Z}
variable (h : Hyp τ Z)

def Hb : Sp k n ≃ₜ TT τ Z × (Fin (dd Z) → k) where
  toFun p := ((⟨p.1 - Pr τ Z p.1, by show D τ Z _ = 0; exact D_sub_Pr h _⟩, p.2), D τ Z p.1)
  invFun q := (q.1.1.1 + E Z ((G τ Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := by
    ext1
    · show p.1 - Pr τ Z p.1 + E Z ((G τ Z)⁻¹ *ᵥ D τ Z p.1) = p.1
      rw [← Pr, sub_add_cancel]
    · rfl
  right_inv q := by
    obtain ⟨⟨⟨y, hy⟩, v⟩, w⟩ := q
    have hy' : D τ Z y = 0 := hy
    have hPy : Pr τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = E Z ((G τ Z)⁻¹ *ᵥ w) := by
      rw [Pr_add, Pr_of_D hy', Pr_E h, zero_add]
    have hDx : D τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = w := by
      rw [D_add, hy', zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]
    refine Prod.ext (Prod.ext (Subtype.ext ?_) rfl) hDx
    show y + E Z ((G τ Z)⁻¹ *ᵥ w) - Pr τ Z (y + E Z ((G τ Z)⁻¹ *ᵥ w)) = y
    rw [hPy, add_sub_cancel_right]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
      ((continuous_D τ Z).comp continuous_fst)
    exact continuous_fst.sub ((continuous_Pr τ Z).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))

def Gm : (Fin (dd Z) → k) ≃ₜ (Fin (dd Z) → k) where
  toFun u := G τ Z *ᵥ u
  invFun u := (G τ Z)⁻¹ *ᵥ u
  left_inv u := by
    show (G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ u) = u
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]
  right_inv u := by
    show G τ Z *ᵥ ((G τ Z)⁻¹ *ᵥ u) = u
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT τ Z × (Fin (dd Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT τ Z)).prodCongr (Gm h)).trans (Hb h).symm

theorem real_test_function_apply (q : TT τ Z × (Fin (dd Z) → k)) : F1 h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]

theorem partial_fourier_first_coordinates (q : TT τ Z × (Fin (dd Z) → k)) : Hb h (F1 h q) = (q.1, G τ Z *ᵥ q.2) := by
  simp only [F1, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

def Gu : GL (Fin (dd Z)) k := Matrix.nonsingInvUnit (G τ Z) (Ne.isUnit (G_det h))

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]

theorem pf_G (F : TT τ Z × (Fin (dd Z) → k) → ℂ) (z : TT τ Z × (Fin (dd Z) → k)) :
    ∫ u, F (z.1, G τ Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) ∂(Measure.pi fun _ => ν) =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
        GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F (z.1, (G τ Z)⁻¹ *ᵥ z.2) := by
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Gu h)
    (fun w => F (z.1, w) * (ψ (((G τ Z)⁻¹ *ᵥ w) ⬝ᵥ z.2) : ℂ))
  have hc : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos).ne'
  have e1 : ∀ u, (Gu h).val *ᵥ u = G τ Z *ᵥ u := fun u => rfl
  have e2 : ∀ u, (G τ Z)⁻¹ *ᵥ (G τ Z *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]
  simp only [e1, e2] at key
  have e3 : ∀ w, ((G τ Z)⁻¹ *ᵥ w) ⬝ᵥ z.2 = w ⬝ᵥ ((G τ Z)⁻¹ *ᵥ z.2) := fun w => by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, G_symm h, dotProduct_comm]
  simp only [e3] at key
  rw [eq_inv_mul_iff_mul_eq₀ hc, key]
  rfl

end PositivityTheory.RgUd.TP.Nil.Four
