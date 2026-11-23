import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigCell.NormalCoord

open GlobalTheory.MixDens.NormalCoord

theorem frame_base {n k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (Gm : V n → Matrix (Fin k) (Fin k) ℂ) (z : V n) (hG : MContDiffAt 2 Gm z)
    (hGp : ∀ᶠ u in 𝓝 z, (Gm u).PosDef) (bL : E →L[ℂ] V n) (X : E → Matrix (Fin k) (Fin k) ℂ)
    (hX : ∀ b c, ContDiff ℂ 2 (fun v => X v b c)) (p : E) (hbp : bL p = z)
    (T : Matrix (Fin k) (Fin k) ℂ) (hXu : IsUnit (X p * T).det) :
    MContDiffAt 2 (fun v => chg (X v * T) (Gm (bL v))) p ∧
      (∀ᶠ v in 𝓝 p, (chg (X v * T) (Gm (bL v))).PosDef) ∧
      (∀ ξ, conn (fun v => chg (X v * T) (Gm (bL v))) p ξ =
        (X p * T)⁻¹ * (conn Gm z (bL ξ) * (X p * T) + mdel X p ξ * T)) ∧
      ∀ ξ η, curv (fun v => chg (X v * T) (Gm (bL v))) p ξ η =
        (X p * T)⁻¹ * curv Gm z (bL ξ) (bL η) * (X p * T) := by
  have hA' : ∀ b c, ContDiff ℂ 2 (fun v => (X v * T) b c) := fun b c => by
    simp only [mul_apply]; exact ContDiff.sum fun d _ => (hX b d).mul contDiff_const
  have hA : MContDiffAt 2 (fun v => X v * T) p := fun b c =>
    (hA' b c).contDiffAt.restrict_scalars ℝ
  have hX1 : MContDiffAt 1 X p := fun b c => ((hX b c).contDiffAt.restrict_scalars ℝ).of_le (by norm_num)
  have hA0 : ∀ x η, mdbar (fun v => X v * T) x η = 0 := fun x η => by
    ext b c
    rw [mdbar_apply, dbar_eq_zero (((hA' b c).differentiable (by norm_num)) x)]
    rfl
  have hG' : MContDiffAt 2 Gm (bL p) := hbp ▸ hG
  have hGb : MContDiffAt 2 (fun v => Gm (bL v)) p := fun b c =>
    (hG' b c).comp p (bL.contDiff.contDiffAt.restrict_scalars ℝ)
  have hGu : IsUnit (Gm (bL p)).det := by rw [hbp]; exact hGp.self_of_nhds.det_pos.ne'.isUnit
  refine ⟨(hA.transpose.mul hGb).mul hA.conjTranspose.transpose, ?_, fun ξ => ?_, fun ξ η => ?_⟩
  · filter_upwards [hA.eventually_isUnit hXu, bL.continuous.continuousAt.eventually (hbp ▸ hGp)] with v h1 h2
    exact posDef_chg ((isUnit_iff_isUnit_det _).2 h1) h2
  · have e1 := conn_changeFrame (hGb.of_le one_le_two) hGu (hA.of_le one_le_two) hXu (hA0 p) ξ
    rw [show (fun v => chg (X v * T) (Gm (bL v))) = fun v => (X v * T)ᵀ * Gm (bL v) * (X v * T)ᴴᵀ from rfl, e1,
      conn_comp_holo (hG'.of_le one_le_two) bL.differentiableAt, bL.fderiv, hbp,
      mdel_mul hX1 (mContDiffAt_const T), mdel_const, Matrix.mul_zero, zero_add]
  · have e1 := curv_changeFrame hGb hGu hA hXu (.of_forall (hA0 ·)) ξ η
    rw [show (fun v => chg (X v * T) (Gm (bL v))) = fun v => (X v * T)ᵀ * Gm (bL v) * (X v * T)ᴴᵀ from rfl, e1,
      curv_comp_holo hG' hGu bL.contDiff.contDiffAt, bL.fderiv, hbp]

section Sesq
variable {E M : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup M] [Module ℂ M]

theorem sesq_zero_left {F : E → E → M} (hF : IsSesq F) (y : E) : F 0 y = 0 := by
  have := hF.smul_left 0 0 y
  rwa [zero_smul, zero_smul] at this

theorem sesq_zero_right {F : E → E → M} (hF : IsSesq F) (x : E) : F x 0 = 0 := by
  have := hF.smul_right 0 x 0
  rwa [zero_smul, map_zero, zero_smul] at this

theorem sesq_sum_left {β : Type} {F : E → E → M} (hF : IsSesq F) (s : Finset β) (x : β → E) (y : E) :
    F (∑ b ∈ s, x b) y = ∑ b ∈ s, F (x b) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_left hF]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hF.add_left, ih]

theorem sesq_sum_right {β : Type} {F : E → E → M} (hF : IsSesq F) (s : Finset β) (x : E) (y : β → E) :
    F x (∑ b ∈ s, y b) = ∑ b ∈ s, F x (y b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_right hF]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hF.add_right, ih]

theorem sesq_sum_sum {β : Type} [Fintype β] {F : E → E → M} (hF : IsSesq F) (e : β → E) (c d : β → ℂ) :
    F (∑ b, c b • e b) (∑ b, d b • e b) = ∑ b, ∑ b', (c b * starRingEnd ℂ (d b')) • F (e b) (e b') := by
  rw [sesq_sum_left hF]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hF.smul_left, sesq_sum_right hF, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [hF.smul_right, smul_smul]

end Sesq

variable {ι : Type} [Fintype ι] {r : ι → ℕ} {n D : ℕ}

theorem baseL_eq_sum (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (ξ : V D) :
    BigCell.baseL ε ξ = ∑ b, ξ (ε.symm (.inl b)) • (EuclideanSpace.single b (1 : ℂ) : V n) := by
  ext k
  simp [BigCell.baseL_apply, BigCell.base, EuclideanSpace.single_apply, Pi.single_apply]

theorem chg_blk (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (L : (Fin n ⊕ (Σ a, Low (r a))) → Fin D → ℂ)
    (N : Matrix (Fin n) (Fin n) ℂ) (δ : (Σ a, Low (r a)) → ℝ) (j l : Fin D) :
    chg (Matrix.of fun k j => L (ε k) j) (BigCell.blk ε N δ) j l =
      (∑ b, ∑ b', L (.inl b) j * N b b' * star (L (.inl b') l)) +
        ∑ s, (δ s : ℂ) * L (.inr s) j * star (L (.inr s) l) := by
  simp only [chg, mul_apply, transpose_apply, conjTranspose_apply, of_apply, BigCell.blk, submatrix_apply]
  rw [← ε.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  have h : ∀ x, ∑ y, L (ε y) j * fromBlocks N 0 0 (diagonal fun s ↦ (δ s : ℂ)) (ε y) x =
      ∑ c, L c j * fromBlocks N 0 0 (diagonal fun s ↦ (δ s : ℂ)) c x :=
    fun x => ε.sum_comp (fun c => L c j * fromBlocks N 0 0 (diagonal fun s ↦ (δ s : ℂ)) c x)
  simp_rw [h]
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
    diagonal_apply, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  exact congrArg₂ (· + ·) Finset.sum_comm (Finset.sum_congr rfl fun s _ => by ring)

set_option maxHeartbeats 2000000 in

theorem normal_coords_base : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (G : ∀ a, V n → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : V n), (∀ a, MContDiffAt ∞ (G a) z) → (∀ a, ∀ᶠ u in 𝓝 z, (G a u).PosDef) → ∃ F : ∀ a, Fin n → Fin n → Matrix (Fin (r a)) (Fin (r a)) ℂ, ∀ u : ∀ a, Low (r a) → ℂ, ∃ (J : Matrix (Fin D) (Fin D) ℂ) (Θ : (Σ a, Fin (r a)) → Matrix (Fin n) (Fin n) ℂ), ‖J.det‖ ^ 2 = ∏ a, jacDens (G a z) (u a) ∧ (∀ (W : Matrix (Fin n) (Fin n) ℂ) (x : Σ a, Fin (r a)), (W * Θ x).trace.re = theta (G x.1 z) (∑ j, ∑ l, W l j • F x.1 j l) (u x.1) x.2) ∧ (∀ x : Σ a, Fin (r a), cHess D (fun v => (BigCell.rootWt ε G x v : ℂ)) (BigCell.pt ε z u) = chg J (BigCell.blk ε (Θ x) fun t => rootDiag 0 x (some t))) ∧ (∀ a, ∑ i, formMat (extTrace (BigCell.stepGram ε G a i) (BigCell.pt ε z u)) = chg J (BigCell.blk ε 0 fun t => bcDiag a (some t))) ∧ ∀ N : Matrix (Fin n) (Fin n) ℂ, chg J (BigCell.blk ε N 0) = BigCell.blk ε N 0 := by
  intro ι _ r n D ε G z hG hP
  let e : Fin n → V n := fun b => EuclideanSpace.single b 1
  have hPz : ∀ a, (G a z).PosDef := fun a => (hP a).self_of_nhds
  have hGu : ∀ a, IsUnit (G a z).det := fun a => (hPz a).det_pos.ne'.isUnit
  have hG2 : ∀ a, MContDiffAt 2 (G a) z := fun a => (hG a).of_le (by norm_cast)
  refine ⟨fun a j l => -((curv (G a) z (e j) (e l))ᵀ * G a z), fun u => ?_⟩
  have hU : ∀ a, IsUnit (uni (u a)) := fun a =>
    (isUnit_iff_isUnit_det _).2 (by rw [GlobalTheory.FlagFibre.det_uni]; exact isUnit_one)
  choose T hT hT1 using fun a => exists_upper_chg_eq_one (posDef_chg (hU a) (hPz a))
  set p := BigCell.pt ε z u with hp
  have hbp : BigCell.base ε p = z := BigCell.base_pt ε z u
  have hfp : BigCell.fib ε p = u := BigCell.fib_pt ε z u
  let bL : V D →L[ℂ] V n := BigCell.baseL ε
  have hbL : ∀ v, BigCell.base ε v = bL v := fun v => rfl
  have hbLs : ∀ ξ, bL ξ = ∑ b, ξ (ε.symm (.inl b)) • e b := fun ξ => baseL_eq_sum ε ξ
  have hbL0 : ∀ y : Σ a, Low (r a), bL (EuclideanSpace.single (ε.symm (.inr y)) (1 : ℂ)) = 0 := fun y => by
    ext b
    simp [bL, BigCell.baseL_apply, BigCell.base, EuclideanSpace.single_apply]
  let X : ∀ a, V D → Matrix (Fin (r a)) (Fin (r a)) ℂ := fun a v => uni (BigCell.fib ε v a)
  have hX : ∀ a b c, ContDiff ℂ 2 (fun v => X a v b c) := by
    intro a b c
    by_cases h : c < b
    · simp only [X, uni, of_apply, dif_pos h, BigCell.fib]
      exact (EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨a, ⟨(b, c), h⟩⟩))).contDiff
    · simp only [X, uni, of_apply, dif_neg h]
      exact contDiff_const
  have hXp : ∀ a, X a p = uni (u a) := fun a => by simp only [X, hfp]
  have hA0u : ∀ a, IsUnit (uni (u a) * T a).det := fun a => by
    have h := congrArg Matrix.det (hT1 a)
    rw [chg_chg, det_chg, det_one] at h
    have : (uni (u a) * T a).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hfr := fun a => frame_base (G a) z (hG2 a) (hP a) bL (X a) (hX a) p (by rw [← hbL, hbp]) (T a)
    (by rw [hXp]; exact hA0u a)
  let H' : ∀ a, V D → Matrix (Fin (r a)) (Fin (r a)) ℂ := fun a v => chg (X a v * T a) (G a (bL v))
  have hH'1 : ∀ a, H' a p = 1 := fun a => by
    show chg (X a p * T a) (G a (bL p)) = 1
    rw [hXp, ← hbL, hbp, ← chg_chg, hT1]
  have hstep : ∀ a i v, (H' a v).submatrix (emb i) (emb i) =
      chg ((T a).submatrix (emb i) (emb i)) (BigCell.stepGram ε G a i v) := fun a i v => by
    rw [BigCell.stepGram, ← chg_submatrix_emb (hT a), chg_chg]
    simp only [H', X, hbL]
  let Lc : (Fin n ⊕ (Σ a, Low (r a))) → V D → ℂ := fun o ξ =>
    Sum.elim (fun b => ξ (ε.symm (.inl b))) (fun y => conn (H' y.1) p ξ y.2.1.1 y.2.1.2) o
  let J : Matrix (Fin D) (Fin D) ℂ := Matrix.of fun k j => Lc (ε k) (EuclideanSpace.single j 1)
  have hchg : ∀ (N : Matrix (Fin n) (Fin n) ℂ) (δ : (Σ a, Low (r a)) → ℝ) (j l : Fin D),
      chg J (BigCell.blk ε N δ) j l =
        (∑ b, ∑ b', (EuclideanSpace.single j (1 : ℂ) : V D) (ε.symm (.inl b)) * N b b' *
          star ((EuclideanSpace.single l (1 : ℂ) : V D) (ε.symm (.inl b')))) +
        ∑ a, ∑ s : Low (r a), (δ ⟨a, s⟩ : ℂ) * conn (H' a) p (EuclideanSpace.single j 1) s.1.1 s.1.2 *
          star (conn (H' a) p (EuclideanSpace.single l 1) s.1.1 s.1.2) := by
    intro N δ j l
    have h0 := chg_blk ε (fun o j => Lc o (EuclideanSpace.single j 1)) N δ j l
    rw [Fintype.sum_sigma] at h0
    exact h0
  have hmdel : ∀ a ξ (b c : Fin (r a)), mdel (X a) p ξ b c =
      if h : c < b then ξ (ε.symm (.inr ⟨a, ⟨(b, c), h⟩⟩)) else 0 := by
    intro a ξ b c
    rw [mdel_apply, del_eq_fderiv (((hX a b c).differentiable (by norm_num)) p)]
    by_cases h : c < b
    · have : (fun v => X a v b c) = ⇑(EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨a, ⟨(b, c), h⟩⟩))) := by
        funext v; simp [X, uni, h, BigCell.fib]
      rw [this, ContinuousLinearMap.fderiv, dif_pos h]
      simp
    · have : (fun v => X a v b c) = fun _ => (if b = c then 1 else 0 : ℂ) := by
        funext v; simp [X, uni, h]
      rw [this, dif_neg h]
      simp
  have hconn : ∀ a ξ, conn (H' a) p ξ = (uni (u a) * T a)⁻¹ *
      (conn (G a) z (bL ξ) * (uni (u a) * T a) + mdel (X a) p ξ * T a) := fun a ξ => by
    rw [← hXp]; exact (hfr a).2.2.1 ξ
  have hcurv : ∀ a ξ η, curv (H' a) p ξ η = (uni (u a) * T a)⁻¹ * curv (G a) z (bL ξ) (bL η) *
      (uni (u a) * T a) := fun a ξ η => by
    rw [← hXp]; exact (hfr a).2.2.2 ξ η
  have hTu : ∀ a, IsUnit (T a).det := fun a => by
    have := hA0u a
    rwa [det_mul, GlobalTheory.FlagFibre.det_uni, one_mul] at this
  have hHf : ∀ a, MContDiffAt 2 (fun v => chg (uni (BigCell.fib ε v a)) (G a (BigCell.base ε v))) p ∧
      ∀ᶠ v in 𝓝 p, (chg (uni (BigCell.fib ε v a)) (G a (BigCell.base ε v))).PosDef := fun a => by
    have h := frame_base (G a) z (hG2 a) (hP a) bL (X a) (hX a) p (by rw [← hbL, hbp]) 1
      (by rw [Matrix.mul_one, hXp, GlobalTheory.FlagFibre.det_uni]; exact isUnit_one)
    have hSg : (fun v => chg (X a v * 1) (G a (bL v))) =
        fun v => chg (uni (BigCell.fib ε v a)) (G a (BigCell.base ε v)) := by
      funext v; simp only [Matrix.mul_one, X, hbL]
    exact ⟨by rw [← hSg]; exact h.1, h.2.1.mono fun v hv => by simpa only [Matrix.mul_one, X, hbL] using hv⟩
  have hT'u : ∀ a (i : Fin (r a)), IsUnit ((T a).submatrix (emb i) (emb i)).det := fun a i => by
    have h := congrArg Matrix.det (hstep a i p)
    rw [hH'1, submatrix_one _ (emb_injective i), det_one, det_chg] at h
    have : ((T a).submatrix (emb i) (emb i)).det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact this.isUnit
  have hT'21 : ∀ a (i : Fin (r a)), ((T a).submatrix (emb i) (emb i)).toBlocks₂₁ = 0 := fun a i => by
    ext x y
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, submatrix_apply, emb, Sum.elim_inl, Sum.elim_inr]
    exact hT a _ _ (by rw [Fin.lt_def, Fin.coe_castLE]; exact y.isLt)
  have hkap : kappa ≠ 0 := by simp [kappa, Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨J, fun x b b' => ((uni (u x.1) * T x.1)⁻¹ * curv (G x.1) z (e b) (e b') * (uni (u x.1) * T x.1)) x.2 x.2,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hsame : ∀ a (s t : Low (r a)),
        conn (H' a) p (EuclideanSpace.single (ε.symm (.inr ⟨a, t⟩)) 1) s.1.1 s.1.2 =
          ((T a)⁻¹ * (uni (u a))⁻¹) s.1.1 t.1.1 * T a t.1.2 s.1.2 := by
      intro a s t
      have hD : mdel (X a) p (EuclideanSpace.single (ε.symm (.inr ⟨a, t⟩)) 1) =
          of fun b c => if b = t.1.1 ∧ c = t.1.2 then 1 else 0 := by
        ext b c
        rw [hmdel, of_apply]
        by_cases h : c < b
        · rw [dif_pos h, EuclideanSpace.single_apply]
          simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
            true_and, Subtype.ext_iff, Prod.ext_iff]
        · rw [dif_neg h, if_neg]
          rintro ⟨rfl, rfl⟩
          exact h t.2
      rw [hconn, hbL0, conn_zero_vec, Matrix.zero_mul, zero_add, hD, Matrix.mul_inv_rev]
      simp [mul_apply, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hdiff : ∀ a (a' : ι) (t : Low (r a')), a' ≠ a →
        conn (H' a) p (EuclideanSpace.single (ε.symm (.inr ⟨a', t⟩)) 1) = 0 := by
      intro a a' t hne
      have hD : mdel (X a) p (EuclideanSpace.single (ε.symm (.inr ⟨a', t⟩)) 1) = 0 := by
        ext b c
        rw [hmdel]
        split_ifs with h
        · rw [EuclideanSpace.single_apply, if_neg]
          · rfl
          simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Sigma.mk.inj_iff]
          exact fun h' => hne h'.1.symm
        · rfl
      rw [hconn, hbL0, conn_zero_vec, Matrix.zero_mul, zero_add, hD, Matrix.zero_mul, Matrix.mul_zero]
    have hM : J.submatrix ε.symm ε.symm =
        fromBlocks 1 0 (Matrix.of fun y b => Lc (.inr y) (EuclideanSpace.single (ε.symm (.inl b)) 1))
          (blockDiagonal' fun a => Matrix.of fun s t : Low (r a) =>
            ((T a)⁻¹ * (uni (u a))⁻¹) s.1.1 t.1.1 * T a t.1.2 s.1.2) := by
      ext (b | ⟨a, s⟩) (b' | ⟨a', t⟩)
      · simp [J, Lc, EuclideanSpace.single_apply, one_apply, eq_comm]
      · simp [J, Lc, EuclideanSpace.single_apply]
      · simp [J]
      · simp only [J, submatrix_apply, of_apply, Equiv.apply_symm_apply, fromBlocks_apply₂₂]
        by_cases h : a' = a
        · subst h
          rw [blockDiagonal'_apply_eq]
          exact hsame a' s t
        · rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]
          simp only [Lc, Sum.elim_inr]
          rw [hdiff a a' t h]
          rfl
    rw [← det_submatrix_equiv_self ε.symm, hM, det_fromBlocks_zero₁₂, det_one, one_mul,
      GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [det_low (u a) (T a) (hT a) (hTu a), norm_prod, ← Finset.prod_pow]
    exact norm_diag_prod_eq_jacDens _ (hPz a) (u a) (T a) (hT a) (hT1 a)
  ·
    rintro W ⟨a, i⟩
    have hF : ∑ j, ∑ l, W l j • (-((curv (G a) z (e j) (e l))ᵀ * G a z)) =
        -((∑ j, ∑ l, W l j • curv (G a) z (e j) (e l))ᵀ * G a z) := by
      simp only [smul_neg, Finset.sum_neg_distrib, transpose_sum, transpose_smul, Finset.sum_mul, Matrix.smul_mul]
    have htr : ∀ M : Matrix (Fin n) (Fin n) ℂ, (W * M).trace = ∑ j, ∑ l, W j l * M l j := fun M => by
      simp [Matrix.trace, mul_apply]
    show _ = theta (G a z) (∑ j, ∑ l, W l j • (-((curv (G a) z (e j) (e l))ᵀ * G a z))) (u a) i
    rw [hF, theta_eq _ _ (u a) (T a) (hT a) (hT1 a)]
    congr 1
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact (htr _).trans Finset.sum_comm
  ·
    rintro ⟨a, i⟩
    set S := fun v => (H' a v).submatrix (emb i) (emb i) with hSdef
    have hS2 : MContDiffAt 2 S p := (hfr a).1.submatrix _ _
    have hS1 : S p = 1 := by
      simp only [hSdef]; rw [hH'1, submatrix_one _ (emb_injective i)]
    have hs1 : subGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1 := by
      ext; simp [subGram, toBlocks₁₁, one_apply]
    have hq1' : quotGram (1 : Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ) = 1 := by
      ext; simp [quotGram, toBlocks₂₁, toBlocks₂₂, toBlocks₁₂, toBlocks₁₁, mul_apply, one_apply]
    have hsub1 : IsUnit (subGram (S p)).det := by
      rw [hS1, hs1, det_one]; exact isUnit_one
    have hq1 : (quotGram (S p)).det.re ≠ 0 := by
      rw [hS1, hq1', det_one]; simp
    set w : V D → ℝ := fun v => -Real.log (quotGram (S v)).det.re with hwdef
    have hw : ContDiffAt ℝ 2 w p :=
      ((Complex.reCLM.contDiff.contDiffAt.comp p (hS2.quotGram hsub1).det).log hq1).neg
    set T' := (T a).submatrix (emb i) (emb i) with hT'def
    have hT'b : T' = fromBlocks T'.toBlocks₁₁ T'.toBlocks₁₂ 0 T'.toBlocks₂₂ := by
      rw [← hT'21 a i, fromBlocks_toBlocks]
    have hdetT' : T'.det = T'.toBlocks₁₁.det * T a i i := by
      conv_lhs => rw [hT'b]
      rw [det_fromBlocks_zero₂₁, det_unique T'.toBlocks₂₂]
      rfl
    have hA1 : IsUnit T'.toBlocks₁₁.det := by
      have := hT'u a i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.1
    have he1 : (fun v => BigCell.rootWt ε G ⟨a, i⟩ v) =ᶠ[𝓝 p] fun v => w v + Real.log (‖T a i i‖ ^ 2) := by
      filter_upwards [(hHf a).2] with v hv
      have hsv : (BigCell.stepGram ε G a i v).PosDef := hv.submatrix (emb_injective i)
      have hsub : IsUnit (subGram (BigCell.stepGram ε G a i v)).det :=
        (posDef_subGram hsv).det_pos.ne'.isUnit
      have hq : quotGram (S v) = chg T'.toBlocks₂₂ (quotGram (BigCell.stepGram ε G a i v)) := by
        simp only [hSdef]
        rw [hstep a i v, ← hT'def, hT'b]
        exact quotGram_chg _ _ hA1 hsub
      have hdet : (quotGram (S v)).det.re = ‖T a i i‖ ^ 2 * (quotGram (BigCell.stepGram ε G a i v)).det.re := by
        rw [hq, det_chg, Complex.re_ofReal_mul, det_unique]
        rfl
      have hpos := det_re_pos (posDef_quotGram hsv)
      have hT2 : ‖T a i i‖ ^ 2 ≠ 0 := by
        have hTii : T a i i ≠ 0 := by
          have := hT'u a i; rw [← hT'def, hdetT', IsUnit.mul_iff] at this; exact this.2.ne_zero
        positivity
      simp only [hwdef, BigCell.rootWt, hdet]
      rw [Real.log_mul hT2 hpos.ne']
      ring
    have hC : ∀ ξ η : V D, curv (H' a) p ξ η i i = ∑ b, ∑ b', ξ (ε.symm (.inl b)) *
        ((uni (u a) * T a)⁻¹ * curv (G a) z (e b) (e b') * (uni (u a) * T a)) i i * star (η (ε.symm (.inl b'))) := by
      intro ξ η
      rw [hcurv, hbLs, hbLs, sesq_sum_sum (isSesq_curv (hG2 a) (hGu a))]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Complex.star_def]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    ext j l
    rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar
      (contDiffAt_ofReal_comp ((hw.add contDiffAt_const).congr_of_eventuallyEq he1)) j l]
    change leviForm (fun v => BigCell.rootWt ε G ⟨a, i⟩ v) p _ _ = _
    rw [leviForm_congr he1, leviForm_add_const _ hw]
    change ddbar (fun v => ((-Real.log (quotGram ((H' a v).submatrix (emb i) (emb i))).det.re : ℝ) : ℂ)) p _ _ = _
    rw [ddbar_rootWt (H' a) p i (hfr a).1 (hfr a).2.1 (hH'1 a), hC]
    refine Eq.trans ?_ (hchg _ (fun t => rootDiag 0 ⟨a, i⟩ (some t)) j l).symm
    have hY : ∑ a', ∑ s : Low (r a'), ((rootDiag 0 ⟨a, i⟩ (some ⟨a', s⟩) : ℝ) : ℂ) *
        conn (H' a') p (EuclideanSpace.single j 1) s.1.1 s.1.2 *
          star (conn (H' a') p (EuclideanSpace.single l 1) s.1.1 s.1.2) =
        ∑ c ∈ Finset.Iio i, conn (H' a) p (EuclideanSpace.single j 1) i c *
            starRingEnd ℂ (conn (H' a) p (EuclideanSpace.single l 1) i c) -
          ∑ c ∈ Finset.Ioi i, conn (H' a) p (EuclideanSpace.single j 1) c i *
            starRingEnd ℂ (conn (H' a) p (EuclideanSpace.single l 1) c i) := by
      rw [Finset.sum_eq_single a]
      · simp only [rootDiag, Option.elim, Sigma.mk.inj_iff, heq_eq_eq, true_and, mul_assoc]
        rw [sum_low_signed (fun b c => conn (H' a) p (EuclideanSpace.single j 1) b c *
          star (conn (H' a) p (EuclideanSpace.single l 1) b c)) i]
        simp only [Complex.star_def]
      · intro b _ hb
        refine Finset.sum_eq_zero fun s _ => ?_
        simp [rootDiag, Sigma.mk.inj_iff, Ne.symm hb]
      · simp
    rw [hY]
    ring
  ·
    intro a
    have hstepT : ∀ i : Fin (r a), extTrace (BigCell.stepGram ε G a i) p =
        extTrace (fun v => (H' a v).submatrix (emb i) (emb i)) p := by
      intro i
      have hK1 : MContDiffAt 1 (BigCell.stepGram ε G a i) p :=
        ((hHf a).1.submatrix (emb i) (emb i)).of_le one_le_two
      have hKp : ∀ᶠ v in 𝓝 p, (BigCell.stepGram ε G a i v).PosDef :=
        (hHf a).2.mono fun v hv => hv.submatrix (emb_injective i)
      rw [← extTrace_chg (A := fun _ => (T a).submatrix (emb i) (emb i)) hK1 hKp
        (mContDiffAt_const _) (hT'u a i) (fun η => mdbar_const _ p η) (.of_forall fun _ => hT'21 a i)]
      congr 1
      funext v
      exact (hstep a i v).symm
    ext j l
    rw [Matrix.sum_apply, hchg 0 (fun t => bcDiag a (some t))]
    simp only [formMat, of_apply, hstepT, extTrace_step (H' a) p _ (hfr a).1 (hfr a).2.1 (hH'1 a),
      mul_div_cancel_left₀ _ hkap, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [← sum_low (fun b c => conn (H' a) p (EuclideanSpace.single j 1) b c *
      starRingEnd ℂ (conn (H' a) p (EuclideanSpace.single l 1) b c))]
    simp only [bcDiag, Option.elim]
    rw [Finset.sum_eq_single a]
    · simp [Complex.star_def]
    · intro b _ hb; simp [hb]
    · simp
  ·
    intro N
    ext j l
    rw [hchg N 0]
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero]
    obtain ⟨c, rfl⟩ := ε.symm.surjective j
    obtain ⟨c', rfl⟩ := ε.symm.surjective l
    rcases c with b | s <;> rcases c' with b' | s' <;>
      simp [BigCell.blk, EuclideanSpace.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.BigCell.NormalCoord
