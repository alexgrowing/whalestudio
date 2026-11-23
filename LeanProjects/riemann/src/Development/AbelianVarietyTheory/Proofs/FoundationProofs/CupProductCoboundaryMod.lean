import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.CupCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem nsub_le_max (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [this]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem det_sq (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := by
  have := congrArg (fun f => ((f s : (Qbar l)ˣ) : Qbar l)) h
  simpa [dt] using this

theorem mat_dual1 (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have hinv : (dt W s)⁻¹ = dt W s := by
    have h2 := congrArg (fun f => f s) h
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h2
    exact inv_eq_of_mul_eq_one_left h2
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, hinv, Units.val_mul]
  simp [dt, eps]

theorem om_smul_right (k : Qbar l) (p q : Fin 2 → Qbar l) : om p (k • q) = k * om p q := by
  simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_mulVec (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (p q : Fin 2 → Qbar l) :
    om (M *ᵥ p) (M *ᵥ q) = M.det * om p q := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_key (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (p q : Fin 2 → Qbar l) :
    om (mat W s *ᵥ p) (mat (dual1 W) s *ᵥ q) = eps l s * om p q := by
  rw [mat_dual1 W h, Matrix.smul_mulVec, om_smul_right, om_mulVec]
  linear_combination (eps l s * om p q) * det_sq W h s

theorem mat_dual1_mul (W : R2 Ω l) (s t : G ℚ Ω) (x : Fin 2 → Qbar l) :
    mat (dual1 W) (s * t) *ᵥ x = mat (dual1 W) s *ᵥ (mat (dual1 W) t *ᵥ x) := by
  simp only [mat, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (x : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM _ _) (hx _)) (mul_mem (hM _ _) (hx _))

theorem om_mem (c : Coef l) (p q : Fin 2 → Qbar l) (hp : ∀ i, p i ∈ c.O) (hq : ∀ i, q i ∈ c.O) : om p q ∈ c.O :=
  sub_mem (mul_mem (hp _) (hq _)) (mul_mem (hp _) (hq _))

theorem dual_representation_integral (c : Coef l) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    (i j : Fin 2) : mat (dual1 W) s i j ∈ c.O := by
  rw [mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem (mul_mem (eps_mem c s) ?_) (hint s i j)
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hint _ _ _) (hint _ _ _)) (mul_mem (hint _ _ _) (hint _ _ _))

theorem mulVec_le {L : ℝ} (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (q : Fin 2 → Qbar l)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) (i : Fin 2) : ‖(M *ᵥ q) i‖ ≤ L := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hM _ _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem om_le_left {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ L) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ‖om p q‖ ≤ L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hp 0)
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) hL).trans (le_of_eq (mul_one L))

theorem om_le_right {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) :
    ‖om p q‖ ≤ L := by
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem ident_a (A v w x B2 B1 B0 : Fin 2 → Qbar l) (e : Qbar l) (key : om w v = e * om x B0) :
    om A v - (e * om x B0 - om x B2 + om x B1) = om (A - (w - x)) v + om x (B2 - (B1 + v)) := by
  simp only [om, Pi.sub_apply, Pi.add_apply] at *
  linear_combination key

theorem ident_b (As At Ast Bt x : Fin 2 → Qbar l) (M P : Matrix (Fin 2) (Fin 2) (Qbar l)) (N : Matrix (Fin 2) (Fin 2) (Qbar l))
    (e : Qbar l) (key : om (P *ᵥ At) (M *ᵥ (N *ᵥ x)) = e * om At (N *ᵥ x)) :
    om As (M *ᵥ Bt) - (e * -om At (N *ᵥ x) - -om Ast (M *ᵥ (N *ᵥ x)) + -om As (M *ᵥ x)) =
      om As (M *ᵥ (Bt - (N *ᵥ x - x))) - om (Ast - (As + P *ᵥ At)) (M *ᵥ (N *ᵥ x)) := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

end GlobalTheory.Ord2.CupCob

namespace GlobalTheory.Ord2.CupCob

theorem cup_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l)
    (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 →
    Coc1 c n W H a → Coc1 c n (dual1 W) H b → (Cob1 c n W H a ∨ Cob1 c n (dual1 W) H b) → Cob2 c n H (cup W a b) := by
  intro l _ Ω _ _ _ c n W H a b hW hint hdet ha hb hcob
  have hWn : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hint s i j)
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := dual_representation_integral c W hdet hint
  have hDn : ∀ s i j, ‖mat (dual1 W) s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hDm s i j)
  have han : ∀ s i, ‖a s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (ha.2.1 s i)
  have hbn : ∀ s i, ‖b s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hb.2.1 s i)
  rcases hcob with ⟨x, hx, hax⟩ | ⟨x, hx, hbx⟩
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    refine ⟨fun t => om x (b t), ?_, fun t => om_mem c _ _ hx (hb.2.1 t), ?_⟩
    · show ContinuousOn (fun t => x 0 * b t 1 - x 1 * b t 0) H
      exact (continuousOn_const.mul (continuousOn_pi.1 hb.1 1)).sub (continuousOn_const.mul (continuousOn_pi.1 hb.1 0))
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s x (b t)
      rw [cup, ident_a (a s) (mat (dual1 W) s *ᵥ b t) (mat W s *ᵥ x) x (b (s * t)) (b s) (b t) (eps l s) key]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_left _ _ (fun i => hax s hs i) (mulVec_le _ _ (hDn s) (hbn t))
      · exact om_le_right _ _ hxn (fun i => hb.2.2 s hs t ht i)
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hD : Continuous fun s => mat (dual1 W) s := by
      have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (mat_dual1 W hdet)
      rw [this]
      exact (eps_cont.mul hM.matrix_det).smul hM
    have hv : Continuous fun s => mat (dual1 W) s *ᵥ x := hD.matrix_mulVec continuous_const
    refine ⟨fun s => -om (a s) (mat (dual1 W) s *ᵥ x), ?_,
      fun s => neg_mem (om_mem c _ _ (ha.2.1 s) (mulVec_mem c _ _ (hDm s) hx)), ?_⟩
    · show ContinuousOn (fun s => -(a s 0 * (mat (dual1 W) s *ᵥ x) 1 - a s 1 * (mat (dual1 W) s *ᵥ x) 0)) H
      exact (((continuousOn_pi.1 ha.1 0).mul ((continuous_apply 1).comp hv).continuousOn).sub
        ((continuousOn_pi.1 ha.1 1).mul ((continuous_apply 0).comp hv).continuousOn)).neg
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s (a t) (mat (dual1 W) t *ᵥ x)
      beta_reduce
      rw [cup, mat_dual1_mul W s t x,
        ident_b (a s) (a t) (a (s * t)) (b t) x (mat (dual1 W) s) (mat W s) (mat (dual1 W) t) (eps l s) key]
      refine (nsub_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_right _ _ (han s) (mulVec_le _ _ (hDn s) (fun i => hbx t ht i))
      · exact om_le_left _ _ (fun i => ha.2.2 s hs t ht i)
          (mulVec_le _ _ (hDn s) (mulVec_le _ _ (hDn t) hxn))

end GlobalTheory.Ord2.CupCob
