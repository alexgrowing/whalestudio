import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicVectorSizeSeenOrthogonalSummandLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeigh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HtMahler

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth Formalism.MainNotions.S Formalism.IndefR.Eqv GlobalTheory.CuspGeo
open scoped NNReal TensorProduct

variable {D : D7}

theorem vsize_seen_mul_le (V : HSp D) (a b : GA D V) {ξ : Fin V.rank → D.host.E} (hξ : ξ ≠ 0) :
    vsize (seen V (a * b) ξ) ≤
      ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) * GlobalTheory.Grow.height V b * vsize (seen V a ξ) := by
  classical
  have hs : seen V (a * b) ξ = Formalism.L2.Theta.mt V b⁻¹ *ᵥ seen V a ξ := by
    simp only [seen, _root_.mul_inv_rev, GlobalTheory.SeenSize.mt_mul, Matrix.mulVec_mulVec]
  have hfx := GlobalTheory.HtOrth.Transp.eventually_vFin_seen_eq_one V a hξ
  have hfy := GlobalTheory.HtOrth.Transp.eventually_vFin_seen_eq_one V (a * b) hξ
  rw [hs] at hfy
  rw [← GlobalTheory.Grow.height_inv, hs]
  set x := seen V a ξ
  set M := Formalism.L2.Theta.mt V b⁻¹
  set hI : InfinitePlace D.host.F → ℝ≥0 := fun w =>
    htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V b⁻¹)) with hIdef
  set hF : HeightOneSpectrum (𝓞 D.host.F) → ℝ≥0 := fun v =>
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V b⁻¹)) with hFdef
  have hIle : ∀ w, vInf w (M *ᵥ x) ≤ ((V.rank : ℝ≥0) + 1) * hI w * vInf w x := fun w =>
    GlobalTheory.SeenSize.vInf_mulVec_le V b⁻¹ w x
  have hFle : ∀ v, vFin v (M *ᵥ x) ≤ hF v * vFin v x := fun v =>
    GlobalTheory.SeenSize.vFin_mulVec_le V b⁻¹ v x
  have hprodI : (∏ w, vInf w (M *ᵥ x)) ≤ ((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) *
      (∏ w, hI w) * ∏ w, vInf w x := by
    calc (∏ w, vInf w (M *ᵥ x)) ≤ ∏ w, (((V.rank : ℝ≥0) + 1) * hI w * vInf w x) :=
          Finset.prod_le_prod (fun _ _ => zero_le) (fun w _ => hIle w)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hsuppF : (Function.mulSupport hF).Finite := finite_mulSupport_htFin D.host.F (matHom V b⁻¹)
  have hsuppx : (Function.mulSupport fun v => vFin v x).Finite := Filter.eventually_cofinite.mp hfx
  have hsuppy : (Function.mulSupport fun v => vFin v (M *ᵥ x)).Finite := Filter.eventually_cofinite.mp hfy
  have hprodF : (∏ᶠ v, vFin v (M *ᵥ x)) ≤ (∏ᶠ v, hF v) * ∏ᶠ v, vFin v x := by
    rw [← finprod_mul_distrib hsuppF hsuppx]
    exact finprod_le_finprod hsuppy (fun _ => zero_le) ((hsuppF.union hsuppx).subset (Function.mulSupport_mul _ _))
      (fun v => hFle v)
  have key : (∏ w, vInf w (M *ᵥ x)) * (∏ᶠ v, vFin v (M *ᵥ x)) ≤
      ((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) * ((∏ w, hI w) * ∏ᶠ v, hF v) *
        ((∏ w, vInf w x) * ∏ᶠ v, vFin v x) := by
    calc _ ≤ (((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) * (∏ w, hI w) * ∏ w, vInf w x) *
          ((∏ᶠ v, hF v) * ∏ᶠ v, vFin v x) := mul_le_mul' hprodI hprodF
      _ = _ := by ring
  have hc : ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) =
      ((((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) : ℝ≥0) : ℝ) := by push_cast; rfl
  show (((∏ w, vInf w (M *ᵥ x)) * ∏ᶠ v, vFin v (M *ᵥ x) : ℝ≥0) : ℝ) ≤
    ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) *
      ((((∏ w, hI w) * ∏ᶠ v, hF v : ℝ≥0)) : ℝ) * ((((∏ w, vInf w x) * ∏ᶠ v, vFin v x : ℝ≥0)) : ℝ)
  rw [hc, ← NNReal.coe_mul, ← NNReal.coe_mul, NNReal.coe_le_coe]
  exact key

theorem vFin_seen_le_one (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) {u : Fin V.rank → D.host.E}
    (hu : ∀ i, IsIntegral ℤ (u i)) (v : HeightOneSpectrum (𝓞 D.host.F)) : vFin v (seen V a u) ≤ 1 := by
  classical
  have ha' : a⁻¹ ∈ GinfC V := inv_mem ha
  have hfin : finHom V a⁻¹ = 1 := ha'
  have h1 : ∀ i j, (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E))
        (Formalism.L2.Theta.mt V a⁻¹ i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j := by
    intro i j
    have e : ((finHom V a⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E))
          (Formalism.L2.Theta.mt V a⁻¹ i j) := rfl
    rw [← e, hfin]
    rfl
  have h2 : ∀ z : AE D, compFin D.host.F D.host.E v z =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E))
        ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp [compFin, evFin]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hent : ∀ i j, compFin D.host.F D.host.E v (Formalism.L2.Theta.mt V a⁻¹ i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) i j := by
    intro i j
    rw [h2, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold vFin
  refine Finset.sup_le fun i _ => ?_
  have hx : compFin D.host.F D.host.E v (seen V a u i) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] u i := by
    unfold seen
    rw [GlobalTheory.SeenSize.mulVec_apply', map_sum]
    simp only [map_mul, hent, GlobalTheory.SeenSize.compFin_incA]
    simp [Matrix.one_apply]
  rw [hx]
  have key := absFin_tmul_le (F := D.host.F) (E := D.host.E) (v := v) (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (⟨u i, hu i⟩ : 𝓞 D.host.E)
  rw [nnnorm_one] at key
  exact key

private theorem infEmb_compInf_eq_theta (V : HSp D) (fr : UI.Frames D V) (w : InfinitePlace D.host.F)
    (θ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hθ : θ = Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) w)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E) :
    infEmb (⟨UI.phiV D w, RingHom.ext fun c => UI.phiV_over D w c⟩ : EmbOver D.host.E w)
      (compInf D.host.F D.host.E w z) = θ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    have e : θ (c ⊗ₜ[D.host.F] x) = Formalism.L2.SG.AdBridge.evV (UI.instV fr) w c * UI.phiV D w x := by
      rw [hθ]
      exact Formalism.L2.SG.AdBridge.thetaV_tmul (UI.instV fr) w c x
    rw [e]
    simp only [compInf, evInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, infEmb_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem map_mt_brg_inv_eq_conj_uMat (V : HSp D) (fr : UI.Frames D V) (y : (UI.instV fr).Ginf)
    (w : InfinitePlace D.host.F) (θ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hθ : θ = Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) w) :
    (Formalism.L2.Theta.mt V (UI.brg fr (y, 1))⁻¹).map θ =
      fr.P w * (uMat ((y w)⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (fr.P w)⁻¹ := by
  have hdet : IsUnit (fr.P w).det := (Matrix.isUnit_iff_isUnit_det _).mp (fr.unit w)
  have hinv : (UI.brg fr) ((y, 1)⁻¹) = (UI.brg fr (y, 1))⁻¹ := map_inv (UI.brg fr) (y, 1)
  have h1 : (uMat ((y w)⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
      (fr.P w)⁻¹ * (Formalism.L2.Theta.mt V (UI.brg fr (y, 1))⁻¹).map θ * fr.P w := by
    rw [hθ, ← hinv]
    exact (UI.brg_isBridge fr ((y, 1)⁻¹)).1 w
  rw [h1]
  set M := (Formalism.L2.Theta.mt V (UI.brg fr (y, 1))⁻¹).map θ
  calc M = (fr.P w * (fr.P w)⁻¹) * M * (fr.P w * (fr.P w)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.mul_one]
    _ = fr.P w * ((fr.P w)⁻¹ * M * fr.P w) * (fr.P w)⁻¹ := by simp only [Matrix.mul_assoc]

theorem vInf_seen_le (V : HSp D) (fr : UI.Frames D V) (y : (UI.instV fr).Ginf) (u : Fin V.rank → D.host.E)
    (w : InfinitePlace D.host.F) :
    (vInf w (seen V (UI.brg fr (y, 1)) u) : ℝ) ≤ (∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ, θ = Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) w := ⟨_, rfl⟩
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hnorm : ∀ (τ : EmbOver D.host.E w) z, ‖infEmb τ (compInf D.host.F D.host.E w z)‖ = ‖θ z‖ := by
    intro τ z
    rcases infEmb_eq_or_conj hcm (⟨UI.phiV D w, RingHom.ext fun c => UI.phiV_over D w c⟩ : EmbOver D.host.E w) τ
      with h | h
    · rw [h]; exact congrArg norm (infEmb_compInf_eq_theta V fr w θ hθ z)
    · rw [h, RingHom.comp_apply, RCLike.norm_conj]; exact congrArg norm (infEmb_compInf_eq_theta V fr w θ hθ z)
  have hvec : ∀ i, θ (seen V (UI.brg fr (y, 1)) u i) = (fr.P w *ᵥ vec (UI.instV fr) y u w) i := by
    intro i
    unfold seen
    rw [RingHom.map_mulVec, map_mt_brg_inv_eq_conj_uMat V fr y w θ hθ]
    have hφ : (θ ∘ fun j => incA D (u j)) = fun j => UI.phiV D w (u j) :=
      funext fun j => by
        show θ (incA D (u j)) = UI.phiV D w (u j)
        rw [hθ]
        exact Formalism.L2.SG.AdBridge.thetaV_inclR (UI.instV fr) w (u j)
    rw [hφ]
    show ((fr.P w * (uMat ((y w)⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (fr.P w)⁻¹) *ᵥ
        fun j => UI.phiV D w (u j)) i =
      (fr.P w *ᵥ ((uMat ((y w)⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *ᵥ
        ((fr.P w)⁻¹ *ᵥ fun j => UI.phiV D w (u j)))) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hc0 : 0 ≤ (∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖ := by positivity
  have key : ∀ (τ : EmbOver D.host.E w) (i : Fin V.rank),
      ‖infEmb τ (compInf D.host.F D.host.E w (seen V (UI.brg fr (y, 1)) u i))‖ ≤
        (∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖ := by
    intro τ i
    rw [hnorm, hvec]
    calc ‖(fr.P w *ᵥ vec (UI.instV fr) y u w) i‖ = ‖∑ j, fr.P w i j * vec (UI.instV fr) y u w j‖ := by
          simp only [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, ‖fr.P w i j * vec (UI.instV fr) y u w j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖fr.P w i j‖ * ‖vec (UI.instV fr) y u‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (vec (UI.instV fr) y u w) j).trans (norm_le_pi_norm (vec (UI.instV fr) y u) w))
            (norm_nonneg _)
      _ = (∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i => ∑ j, ‖fr.P w i j‖) (fun i _ => by positivity)
            (Finset.mem_univ i)) (norm_nonneg _)
  have hsup : vInf w (seen V (UI.brg fr (y, 1)) u) ≤
      ((∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖).toNNReal := by
    unfold vInf
    refine Finset.sup_le fun p _ => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hc0]
    exact key p.1 p.2
  calc (vInf w (seen V (UI.brg fr (y, 1)) u) : ℝ)
      ≤ (((∑ i, ∑ j, ‖fr.P w i j‖) * ‖vec (UI.instV fr) y u‖).toNNReal : ℝ) := NNReal.coe_le_coe.mpr hsup
    _ = _ := Real.coe_toNNReal _ hc0

theorem exists_vsize_le (V : HSp D) (fr : UI.Frames D V) (B : ℝ) : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (y : (UI.instV fr).Ginf) (b : GA D V), GlobalTheory.Grow.height V b ≤ B → ∀ u : Fin V.rank → D.host.E,
      (∀ i, IsIntegral ℤ (u i)) → u ≠ 0 → ‖vec (UI.instV fr) y u‖ ≤ 1 →
        vsize (seen V (UI.brg fr (y, 1) * b) u) ≤ A * ‖vec (UI.instV fr) y u‖ := by
  classical
  set K : ℝ := ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) with hK
  set Q : ℝ := ∏ w, ∑ i, ∑ j, ‖fr.P w i j‖ with hQ
  have hK0 : 0 ≤ K := by positivity
  have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun w _ => by positivity
  refine ⟨max 1 (K * max B 0 * Q), le_max_left _ _, ?_⟩
  intro y b hb u hu hu0 hr1
  set a := UI.brg fr (y, 1)
  set r := ‖vec (UI.instV fr) y u‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ha : a ∈ GinfC V := (Formalism.IndefR.Eqv.brg_mem_GinfC fr (y, 1)).mpr rfl
  have hfin : (∏ᶠ v, vFin v (seen V a u) : ℝ≥0) ≤ 1 :=
    finprod_induction (fun z : ℝ≥0 => z ≤ 1) le_rfl (fun x y hx hy => mul_le_one' hx hy)
      (fun v => vFin_seen_le_one V ha hu v)
  have hinf : (∏ w, (vInf w (seen V a u) : ℝ)) ≤ Q * r ^ Fintype.card (InfinitePlace D.host.F) := by
    calc (∏ w, (vInf w (seen V a u) : ℝ)) ≤ ∏ w, ((∑ i, ∑ j, ‖fr.P w i j‖) * r) :=
          Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) (fun w _ => vInf_seen_le V fr y u w)
      _ = Q * r ^ Fintype.card (InfinitePlace D.host.F) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card (InfinitePlace D.host.F) ≠ 0 := Fintype.card_ne_zero
  have hpow : r ^ Fintype.card (InfinitePlace D.host.F) ≤ r := pow_le_of_le_one hr0 hr1 hcard
  have hsa : vsize (seen V a u) ≤ Q * r := by
    have e : vsize (seen V a u) = (∏ w, (vInf w (seen V a u) : ℝ)) * ((∏ᶠ v, vFin v (seen V a u) : ℝ≥0) : ℝ) := by
      simp only [vsize, NNReal.coe_mul, NNReal.coe_prod]
    rw [e]
    have hf' : ((∏ᶠ v, vFin v (seen V a u) : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast hfin
    calc (∏ w, (vInf w (seen V a u) : ℝ)) * ((∏ᶠ v, vFin v (seen V a u) : ℝ≥0) : ℝ)
        ≤ (Q * r ^ Fintype.card (InfinitePlace D.host.F)) * 1 :=
          mul_le_mul hinf hf' (NNReal.coe_nonneg _) (mul_nonneg hQ0 (pow_nonneg hr0 _))
      _ ≤ Q * r := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hpow hQ0
  have hb' : GlobalTheory.Grow.height V b ≤ max B 0 := hb.trans (le_max_left _ _)
  have hh0 : 0 ≤ GlobalTheory.Grow.height V b := (GlobalTheory.Grow.height_pos V b).le
  calc vsize (seen V (a * b) u) ≤ K * GlobalTheory.Grow.height V b * vsize (seen V a u) := vsize_seen_mul_le V a b hu0
    _ ≤ K * max B 0 * (Q * r) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb' hK0) hsa (GlobalTheory.HtOrth.vsize_nonneg _)
          (mul_nonneg hK0 (le_max_right _ _))
    _ = (K * max B 0 * Q) * r := by ring
    _ ≤ max 1 (K * max B 0 * Q) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr0

theorem quotHeight_le_of_no_short : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 →
    (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) →
      GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C := by
  intro D V
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      IsInfFam θ :=
    ⟨fun ρ => GlobalTheory.AutFunCompare.infEmb D.sp.cm (tauE D ρ),
      fun ρ => GlobalTheory.AutFunCompare.isInfEmb_infEmb D.sp.cm (tauE D ρ)⟩
  let fr := UI.framesV D V
  obtain ⟨hGQ, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨S, hS0, hS⟩ := GlobalTheory.CuspGeo.brg_entry_bounds fr h2
  obtain ⟨-, Ch, d, hCh⟩ := GlobalTheory.Grow.normInf_height_comparison D V θ hθ
  obtain ⟨b0, C0, δ0, K, hδ0, hK, hred⟩ :=
    GlobalTheory.CuspGeo.nearInst (UI.instV fr) ⊤ isOpen_univ
  obtain ⟨b1, C1, K1, hK1, hmin⟩ := GlobalTheory.htMin_of_reduced (UI.instV fr)
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (GlobalTheory.CuspGeo.continuous_brgFin fr))
  obtain ⟨B2, hB2⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (((hK1.prod hK).image continuous_mul).image (GlobalTheory.CuspGeo.continuous_brgFin fr))
  obtain ⟨A, hA1, hA⟩ := exists_vsize_le V fr B
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  refine ⟨max Ch 0 * ((1 + S * max C1 1) * A ^ b1) ^ d * max B2 1, b1 * d, ?_⟩
  intro g t ht0 ht1 hno
  obtain ⟨δ, -, -, ⟨γ1, hγ1, hk, -⟩, -⟩ := hred ((UI.brg fr).symm g)
  have hγ1Q : UI.brg fr γ1 ∈ GQ V := (hGQ γ1).mpr hγ1
  have hbx : UI.brg fr (γ1 * (UI.brg fr).symm g) = UI.brg fr γ1 * g := by
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hprod : UI.brg fr ((γ1 * (UI.brg fr).symm g).1, 1) * UI.brg fr (1, (γ1 * (UI.brg fr).symm g).2) =
      UI.brg fr γ1 * g := by
    rw [← map_mul, ← hbx]
    exact congrArg (UI.brg fr) (Prod.ext (mul_one _) (one_mul _))
  have hbk : GlobalTheory.Grow.height V (UI.brg fr (1, (γ1 * (UI.brg fr).symm g).2)) ≤ B :=
    hB _ ⟨_, hk, GlobalTheory.CuspGeo.brgFin_apply fr _⟩
  have htA0 : 0 < t / A := div_pos ht0 hA0
  have htA1 : t / A ≤ 1 := div_le_one_of_le₀ (ht1.trans hA1) hA0.le
  have hns : GlobalTheory.CuspGeo.NoShort (UI.instV fr) (γ1 * (UI.brg fr).symm g).1 (t / A) := by
    intro u hu hu0
    by_contra hlt
    push Not at hlt
    have hle1 : ‖vec (UI.instV fr) (γ1 * (UI.brg fr).symm g).1 u‖ ≤ 1 := hlt.le.trans htA1
    have h1 := hA (γ1 * (UI.brg fr).symm g).1 (UI.brg fr (1, (γ1 * (UI.brg fr).symm g).2)) hbk u hu hu0 hle1
    rw [hprod] at h1
    obtain ⟨η, hη0, hη⟩ := GlobalTheory.SeenSize.exists_seen_mul (inv_mem hγ1Q) (UI.brg fr γ1 * g) hu0
    rw [inv_mul_cancel_left] at hη
    have h3 := hno η hη0
    rw [hη] at h3
    have h4 : A * ‖vec (UI.instV fr) (γ1 * (UI.brg fr).symm g).1 u‖ < t := by
      calc A * ‖vec (UI.instV fr) (γ1 * (UI.brg fr).symm g).1 u‖ < A * (t / A) :=
            mul_lt_mul_of_pos_left hlt hA0
        _ = t := by field_simp
    linarith
  obtain ⟨γ2, hγ2, hk2, hent⟩ := hmin (γ1 * (UI.brg fr).symm g).1 (t / A) htA0 htA1 hns
  have hγ2Q : UI.brg fr γ2 ∈ GQ V := (hGQ γ2).mpr hγ2
  have hT0 : 0 < (t / A) ^ b1 := pow_pos htA0 _
  have hc1 : (1 : ℝ) ≤ max C1 1 := le_max_right _ _
  have hentc : ∀ v i j, ‖uMat ((γ2.1 * (γ1 * (UI.brg fr).symm g).1) v) i j‖ ≤ max C1 1 / (t / A) ^ b1 :=
    fun v i j => by
      rw [le_div_iff₀ hT0]
      exact (hent v i j).trans (le_max_left _ _)
  have hc0 : 0 ≤ max C1 1 / (t / A) ^ b1 := div_nonneg (zero_le_one.trans hc1) hT0.le
  have hnI := (hS (γ2.1 * (γ1 * (UI.brg fr).symm g).1) (max C1 1 / (t / A) ^ b1)).1 hentc
  have hmemI : UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1) ∈ GinfC V :=
    (Formalism.IndefR.Eqv.brg_mem_GinfC fr _).mpr rfl
  have hN0 : 0 ≤ Formalism.L2.Theta.normInf θ V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1)) := by
    unfold Formalism.L2.Theta.normInf
    positivity
  have hCh0 : (0 : ℝ) ≤ max Ch 0 := le_max_right _ _
  have hH1 : GlobalTheory.Grow.height V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1)) ≤
      max Ch 0 * (1 + S * (max C1 1 / (t / A) ^ b1)) ^ d := by
    calc _ ≤ Ch * (1 + Formalism.L2.Theta.normInf θ V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1))) ^ d :=
          hCh _ hmemI
      _ ≤ max Ch 0 * (1 + Formalism.L2.Theta.normInf θ V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1))) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
      _ ≤ max Ch 0 * (1 + S * (max C1 1 / (t / A) ^ b1)) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) d) hCh0
  have hbk2 : GlobalTheory.Grow.height V (UI.brg fr (1, γ2.2 * (γ1 * (UI.brg fr).symm g).2)) ≤ max B2 1 :=
    (hB2 _ ⟨_, ⟨(γ2.2, (γ1 * (UI.brg fr).symm g).2), ⟨hk2, hk⟩, rfl⟩, GlobalTheory.CuspGeo.brgFin_apply fr _⟩).trans
      (le_max_left _ _)
  have hsplit : UI.brg fr γ2 * UI.brg fr γ1 * g =
      UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1) * UI.brg fr (1, γ2.2 * (γ1 * (UI.brg fr).symm g).2) := by
    rw [mul_assoc, ← hbx, ← map_mul, ← map_mul]
    exact congrArg (UI.brg fr) (Prod.ext (mul_one _).symm (one_mul _).symm)
  have hq : GlobalTheory.Grow.quotHeight V g ≤ max Ch 0 * (1 + S * (max C1 1 / (t / A) ^ b1)) ^ d * max B2 1 := by
    calc GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr γ2 * UI.brg fr γ1 * g) :=
          GlobalTheory.Grow.quotHeight_le V g (mul_mem hγ2Q hγ1Q)
      _ = GlobalTheory.Grow.height V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1) *
            UI.brg fr (1, γ2.2 * (γ1 * (UI.brg fr).symm g).2)) := by rw [hsplit]
      _ ≤ GlobalTheory.Grow.height V (UI.brg fr (γ2.1 * (γ1 * (UI.brg fr).symm g).1, 1)) *
            GlobalTheory.Grow.height V (UI.brg fr (1, γ2.2 * (γ1 * (UI.brg fr).symm g).2)) := GlobalTheory.Grow.height_mul_le V _ _
      _ ≤ (max Ch 0 * (1 + S * (max C1 1 / (t / A) ^ b1)) ^ d) * max B2 1 :=
          mul_le_mul hH1 hbk2 (GlobalTheory.Grow.height_pos V _).le (mul_nonneg hCh0 (pow_nonneg (by positivity) _))
  have htb : 0 < t ^ b1 := pow_pos ht0 _
  have htb1 : t ^ b1 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hAb : 1 ≤ A ^ b1 := one_le_pow₀ hA1
  have hcT : max C1 1 / (t / A) ^ b1 * t ^ b1 = max C1 1 * A ^ b1 := by
    rw [div_pow]
    field_simp
  have hkey : (1 + S * (max C1 1 / (t / A) ^ b1)) * t ^ b1 ≤ (1 + S * max C1 1) * A ^ b1 := by
    have e : (1 + S * (max C1 1 / (t / A) ^ b1)) * t ^ b1 = t ^ b1 + S * (max C1 1 * A ^ b1) := by
      rw [← hcT]; ring
    rw [e]
    nlinarith
  calc GlobalTheory.Grow.quotHeight V g * t ^ (b1 * d)
      ≤ (max Ch 0 * (1 + S * (max C1 1 / (t / A) ^ b1)) ^ d * max B2 1) * (t ^ b1) ^ d := by
        rw [pow_mul]
        exact mul_le_mul_of_nonneg_right hq (pow_nonneg htb.le _)
    _ = max Ch 0 * max B2 1 * ((1 + S * (max C1 1 / (t / A) ^ b1)) * t ^ b1) ^ d := by rw [mul_pow]; ring
    _ ≤ max Ch 0 * max B2 1 * ((1 + S * max C1 1) * A ^ b1) ^ d := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCh0 (by positivity))
        exact pow_le_pow_left₀ (by positivity) hkey d
    _ = max Ch 0 * ((1 + S * max C1 1) * A ^ b1) ^ d * max B2 1 := by ring

end GlobalTheory.HtMahler

end
