import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.ReNonnegPsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem b_qR_single {L : Type} [Field L] [NumberField L] {N : ℕ} [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem b_cl_at {L : Type} [Field L] [NumberField L] {N : ℕ} {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [b_qR_single, b_qR_single] at this

private theorem b_toR_ne {L : Type} [Field L] [NumberField L] {N : ℕ} {v : Lat L N} (hv : v ≠ 0) :
    toR v ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
  obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
  intro h0
  have := congrFun (congrFun h0 w) a
  simp only [toR, Pi.zero_apply] at this ha
  apply ha
  simpa [embO] using this

private theorem b_qR_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N} (hh : h ∈ Pos L N)
    {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N h hh
  have h1 := hev.self_of_nhds z
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 0 < ‖z‖ ^ 2 := by positivity
  nlinarith

private theorem b_emb_val {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem b_ginv {L : Type} [Field L] [NumberField L] {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← b_emb_val, map_inv, Pi.inv_apply]

private theorem b_transp {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    star z ⬝ᵥ (Mᵀ *ᵥ z) = star (star z) ⬝ᵥ (M *ᵥ star z) := by
  rw [star_star, mulVec_transpose, dotProduct_comm (star z), ← dotProduct_mulVec]

theorem pf_Basic : Basic := by
  intro L _ _ N hN
  classical
  refine ⟨?p1, ?p2, ?p3, ?p4, ?p5, ?p6⟩
  · intro h hh
    have hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite := fun B => by
      obtain ⟨S, hS, hev⟩ := UpperTheory.V.KT.locfin L N h hh B
      refine hS.subset fun v hv => ?_
      by_contra hvS
      exact absurd hv (not_le.2 (hev.self_of_nhds v hvS))
    have hpos : ∀ v : Lat L N, v ≠ 0 → 0 < q h v := fun v hv => b_qR_pos hh (b_toR_ne hv)
    obtain ⟨v0, hv0⟩ : ∃ v0 : Lat L N, v0 ≠ 0 := by
      refine ⟨Pi.single (⟨0, hN⟩ : Fin N) 1, fun h0 => ?_⟩
      have := congrFun h0 ⟨0, hN⟩
      simp at this
    obtain ⟨vm, ⟨hvm0, -⟩, hvm⟩ := Set.exists_min_image {v : Lat L N | v ≠ 0 ∧ q h v ≤ q h v0}
      (fun v => q h v) ((hfin (q h v0)).subset fun v hv => hv.2) ⟨v0, hv0, le_rfl⟩
    have mlow : ∀ v : Lat L N, v ≠ 0 → q h vm ≤ q h v := fun v hv => by
      by_cases hle : q h v ≤ q h v0
      · exact hvm v ⟨hv, hle⟩
      · exact (hvm v0 ⟨hv0, le_rfl⟩).trans (not_le.1 hle).le
    haveI : Nonempty {y : Lat L N // y ≠ 0} := ⟨⟨v0, hv0⟩⟩
    have hlam : lam h = q h vm := by
      unfold lam
      refine le_antisymm (ciInf_le ⟨q h vm, ?_⟩ (⟨vm, hvm0⟩ : {y : Lat L N // y ≠ 0}))
        (le_ciInf fun y => mlow y.1 y.2)
      rintro _ ⟨y, rfl⟩
      exact mlow y.1 y.2
    refine ⟨by rw [hlam]; exact hpos vm hvm0, fun v hv => by rw [hlam]; exact mlow v hv,
      ⟨vm, hvm0, hlam.symm⟩, fun w => ?_, hfin⟩
    exact (hh w).inv.transpose
  · intro γ h v
    simp only [q, qR, ac, mat_actL, smul_lat, toR_mulVec, b_ginv]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  · intro γ
    let γt : Gm L N := ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
      by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    refine ⟨γt⁻¹, fun h hh => HS_ext fun w => ?_⟩
    simp only [dualH, mat_mkHS, ac, mat_actL, b_ginv, inv_inv]
    have hT : ((γt : Matrix (Fin N) (Fin N) (𝓞 L))).map (embO w) =
        ((γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w))ᵀ := by
      ext i j; rfl
    rw [hT]
    set M := (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hM
    set G := ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hG
    have hMG : M * G = 1 := by
      rw [hM, hG, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hGinv : G⁻¹ = M := Matrix.inv_eq_left_inv hMG
    have hCT : Mᴴᵀ = Mᵀᴴ := by ext i j; simp
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hGinv, ← conjTranspose_nonsing_inv, hGinv,
      transpose_mul, transpose_mul, hCT]
  · intro δ hδ hδ2 h hh k hcl
    have hat := fun w x => b_cl_at hcl w x
    have hk : k ∈ Pos L N := fun w => by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm k w) (by
        intro x hx
        have h1 := (Complex.pos_iff.1 ((hh w).dotProduct_mulVec_pos hx)).1
        have h2 := (abs_le.1 (hat w x)).1
        exact Complex.pos_iff.2 ⟨by nlinarith, (herm_im _ (mat_herm k w) x).symm⟩)
    refine ⟨hk, fun z => ?_⟩
    have per : ∀ w, |(star (z w) ⬝ᵥ (mat (dualH k) w *ᵥ z w)).re -
        (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re| ≤
        2 * δ * (star (z w) ⬝ᵥ (mat (dualH h) w *ᵥ z w)).re := by
      intro w
      simp only [dualH, mat_mkHS]
      rw [b_transp, b_transp]
      have i1 := invmono (mat h w) (mat k w) (hh w) (hk w) (1 - δ) (by linarith)
        (fun x => by have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith) (star (z w))
      have i2 := invmono (mat k w) (mat h w) (hk w) (hh w) (1 + δ)⁻¹ (by positivity)
        (fun x => by
          rw [inv_mul_le_iff₀ (by linarith)]
          have := (abs_le.1 (hat w x)).2
          rw [add_mul, one_mul]; linarith) (star (z w))
      have hD := re_nonneg_psd (hh w).inv.posSemidef (star (z w))
      have i2' := mul_le_mul_of_nonneg_left i2 (by linarith : (0 : ℝ) ≤ 1 + δ)
      rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul] at i2'
      refine abs_le.2 ⟨by nlinarith [mul_nonneg hδ hD], by nlinarith [mul_nonneg hδ hD]⟩
    unfold qR
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => per w)
  · intro δ hδ h hh k hcl w u v
    have hat := fun x => b_cl_at hcl w x
    have hA : (mat k w - mat h w).IsHermitian := (mat_herm k w).sub (mat_herm h w)
    have hb : ∀ x : Fin N → ℂ, |(star x ⬝ᵥ ((mat k w - mat h w) *ᵥ x)).re| ≤
        δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
      intro x; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]; exact hat x
    have := csq _ _ hA (hh w).posSemidef δ hδ hb u v
    rw [sub_mulVec, dotProduct_sub] at this
    have ha := re_nonneg_psd (hh w).posSemidef u
    have hb' := re_nonneg_psd (hh w).posSemidef v
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) ha) hb']
  · obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (𝕜 := ℝ) (HSsub L N)
    have hent : ∀ w a b, ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := fun w a b => by
      have e : (fun h : HS L N => mat h w a b) =
          (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
      rw [e]
      exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp
        (HSsub L N).subtypeL.contDiff
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun h : HS L N => ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)) (Pos L N) := by
      refine contDiffOn_pi' fun w => contDiffOn_pi' fun a => contDiffOn_pi' fun b => ?_
      intro h hh
      have hdet : (mat h w).det ≠ 0 := ((hh w).det_pos).ne'
      exact (cd_inv (fun h : HS L N => mat h w) (fun i j => hent w i j) b a h hdet).contDiffWithinAt
    have e : (dualH : HS L N → HS L N) =
        fun h => P ((dualH h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
      funext h; exact (hP (dualH h)).symm
    rw [e]
    exact P.contDiff.comp_contDiffOn hF

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
