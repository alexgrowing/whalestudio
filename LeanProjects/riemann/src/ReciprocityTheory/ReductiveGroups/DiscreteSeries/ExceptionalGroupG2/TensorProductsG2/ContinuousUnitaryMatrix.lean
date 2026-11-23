import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.HasDerivAtInvExpCurveEntry
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem tensor_group_mul_kDiag (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  have h1 : kᴴ * k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hkU : k ∈ UJset ε := by
    show kᴴ * _ * k = _
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hσm : σ (g * k) = (σ g).comp (σ k) := hσ.1.2 g hg k hkU
  funext c
  simp only [tensGrp, kDiag, hσm, ContinuousLinearMap.comp_apply, map_sum, map_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  cases dual
  · simp only [cond_false, Matrix.mul_apply]
  · have hkinv : k⁻¹ = star k := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
    simp only [cond_true, Matrix.mul_inv_rev, hkinv, Matrix.mul_apply, Matrix.star_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring

theorem tensor_phi_of_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    oa1Phi dual g c d =
      cond dual ((if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1)) (g c d) := by
  cases dual
  · rfl
  · unfold inUJ at hg
    simp only [PI.UpqRep.Jm, Formalism.REAL.Jm, ReciprocityTheory.ChartRestriction.DS.Jm] at hg
    set J : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then (1 : ℂ) else -1 with hJdef
    have hJJ : J * J = 1 := by
      rw [hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      split_ifs <;> norm_num
    have hinv : g⁻¹ = J * gᴴ * J := by
      apply Matrix.inv_eq_left_inv
      calc J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hJJ]
    show g⁻¹ d c = (if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1)
    rw [hinv, hJdef, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem norm_tensor_phi_le_sqrt_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    ‖oa1Phi dual g c d‖ ≤ Real.sqrt (S7.hs g) := by
  have key : ‖g c d‖ ≤ Real.sqrt (S7.hs g) := by
    calc ‖g c d‖ = |‖g c d‖| := (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (S7.hs g) := Real.abs_le_sqrt ?_
    show ‖g c d‖ ^ 2 ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2
    calc ‖g c d‖ ^ 2 ≤ ∑ j, ‖g c j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖g c j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ d)
      _ ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2) (fun i _ => by positivity)
            (Finset.mem_univ c)
  rw [tensor_phi_of_unitary hg dual c d]
  cases dual
  · exact key
  · have hs : ∀ a : Fin n, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    show ‖(if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1)‖ ≤ _
    rw [norm_mul, norm_mul, hs, hs, norm_star, one_mul, mul_one]
    exact key

theorem smoothOnG_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) : Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, F i x) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩
  · intro i s hi ih h
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    intro g₀ hg₀
    obtain ⟨U1, F1, hU1, hg1, hF1, he1⟩ := h1 g₀ hg₀
    obtain ⟨U2, F2, hU2, hg2, hF2, he2⟩ := h2 g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
      (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
    show ∑ j ∈ insert i s, F j g = F1 g + F2 g
    rw [Finset.sum_insert hi, he1 g hg.1 hgJ]
    exact congrArg (F1 g + ·) (he2 g hg.2 hgJ)

theorem smoothOnG_inner_rep (w : H) {v : H} (hv : IsSmoothVecU ε σ v) :
    Formalism.REAL.SmoothOnG ε (fun g => inner ℂ w (σ g v)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, he⟩ := hv g₀ hg₀
  exact ⟨U, fun g => inner ℂ w (F g), hU, hg, contDiffOn_const.inner ℂ hF,
    fun g hgU hgJ => congrArg (inner ℂ w) (he g hgU hgJ)⟩

theorem smoothOnG_tensor_phi (dual : Bool) (c d : Fin n) : Formalism.REAL.SmoothOnG ε (fun g => oa1Phi dual g c d) := by
  have hentry : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => g c d :=
    (contDiff_apply ℝ ℂ d).comp (contDiff_apply ℝ (Fin n → ℂ) c)
  have hstar : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => star (g c d) :=
    Complex.conjCLE.contDiff.comp hentry
  intro g₀ _
  cases dual
  · exact ⟨Set.univ, fun g => g c d, isOpen_univ, Set.mem_univ _, hentry.contDiffOn, fun g _ _ => rfl⟩
  · refine ⟨Set.univ, fun g => (if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1),
      isOpen_univ, Set.mem_univ _, ((contDiff_const.mul hstar).mul contDiff_const).contDiffOn,
      fun g _ hg => tensor_phi_of_unitary hg true c d⟩

private theorem smoothOnG_mul' {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F)
    (hG : Formalism.REAL.SmoothOnG ε G) : Formalism.REAL.SmoothOnG ε (fun x => F x * G x) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, he1⟩ := hF g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, he2⟩ := hG g₀ hg₀
  refine ⟨U1 ∩ U2, fun x => F1 x * F2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).mul (hF2.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  show F g * G g = F1 g * F2 g
  rw [he1 g hg.1 hgJ, he2 g hg.2 hgJ]

theorem tensor_coef_smooth (dual : Bool) (η f : Fin n → H) (hf : ∀ d, IsSmoothVecU ε σ (f d)) :
    Formalism.REAL.SmoothOnG ε (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) := by
  have heq : (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) =
      fun g => ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
    funext g
    simp only [tensGrp, inner_sum, inner_smul_right, oa1Phi]
  rw [heq]
  exact smoothOnG_finset_sum _ _ fun c _ => smoothOnG_finset_sum _ _ fun d _ =>
    smoothOnG_mul' (smoothOnG_tensor_phi dual c d) (smoothOnG_inner_rep (η c) (hf d))

theorem continuous_umat' : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_rep_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := by
  exact (hσ.2.2 v).comp_continuous continuous_umat' fun g => Formalism.MainNotions.BridgeCSchur.umat_mem g

theorem continuous_tensor_phi (dual : Bool) (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => oa1Phi dual (Formalism.MainNotions.S.umat g) c d) := by
  have hU : ∀ g : Formalism.REAL.UJ ε, inUJ ε (Formalism.MainNotions.S.umat g) := fun g => Formalism.MainNotions.BridgeCSchur.umat_mem g
  have he : Continuous fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g c d := continuous_umat'.matrix_elem c d
  cases dual
  · exact he
  · have hfun : (fun g : Formalism.REAL.UJ ε => oa1Phi true (Formalism.MainNotions.S.umat g) c d) = fun g =>
        (if ε d then (1 : ℂ) else -1) * star (Formalism.MainNotions.S.umat g c d) * (if ε c then (1 : ℂ) else -1) :=
      funext fun g => tensor_phi_of_unitary (hU g) true c d
    rw [hfun]
    exact (continuous_const.mul he.star).mul continuous_const

theorem tensor_term_memLp (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (dual : Bool) {w v : D} (hw : w ∈ S) (hv : v ∈ S) (c d : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      oa1Phi dual (Formalism.MainNotions.S.umat g) c d * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε) := by
  have hU : ∀ g : Formalism.REAL.UJ ε, inUJ ε (Formalism.MainNotions.S.umat g) := fun g => Formalism.MainNotions.BridgeCSchur.umat_mem g
  refine (hW v hv w hw).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner (continuous_rep_orbit hσ _))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs (hU g) dual c d) (norm_nonneg _)

theorem tensor_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) = fun g =>
      ∑ c, ∑ d, oa1Phi dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ ((η c : D) : H) (σ (Formalism.MainNotions.S.umat g) ((f d : D) : H)) :=
    funext fun g => tensor_coef_expand dual σ _ _ _
  rw [e]
  rw [tset_mem] at hη hf
  exact memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => tensor_term_memLp hσ hW dual (hη c) (hf d) c d

end ReciprocityTheory.ChartRestriction.DS.G2
