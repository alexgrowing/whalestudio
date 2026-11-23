import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchLim.ChTwoDens

theorem alt_sum {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (T : (n → n) → ℂ) :
    ∑ s : Equiv.Perm n, ((Equiv.Perm.sign s : ℤ) : ℂ) * ∑ f : n → n, (∏ i, J (f i) (s i)) * T f =
      J.det * ∑ s : Equiv.Perm n, ((Equiv.Perm.sign s : ℤ) : ℂ) * T s := by
  have h₁ (f : n → n) : ∑ s : Equiv.Perm n, ((Equiv.Perm.sign s : ℤ) : ℂ) * ((∏ i, J (f i) (s i)) * T f) =
      (J.submatrix f id).det * T f := by
    rw [← det_transpose, det_apply', Finset.sum_mul]
    simp [mul_assoc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [h₁]
  refine (Finset.sum_of_injOn (fun s : Equiv.Perm n => (s : n → n)) (fun _ _ _ _ h => Equiv.coe_fn_injective h)
    (fun _ _ => Finset.mem_univ _) (fun f _ hf => ?_) fun s _ => ?_).symm
  · have hn : ¬ Function.Injective f := fun hi =>
      hf ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hi), by simp, rfl⟩
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hn
    rw [det_zero_of_row_eq hne (by ext j; simp [hab]), zero_mul]
  · rw [det_permute]
    push_cast
    ring

theorem alt_sum_two {e : ℕ} (J B : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ) (C : Fin e → Fin (e + 2) → ℂ) :
    ∑ s : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ((∑ a, ∑ c, J a (s 0) * J c (s 1) * B a c) * ∏ i : Fin e, ∑ a, J a (s i.succ.succ) * C i a) =
      J.det * ∑ s : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        (B (s 0) (s 1) * ∏ i : Fin e, C i (s i.succ.succ)) := by
  rw [← alt_sum J fun f => B (f 0) (f 1) * ∏ i : Fin e, C i (f i.succ.succ)]
  refine Finset.sum_congr rfl fun s _ => congrArg _ ?_
  rw [Fintype.prod_sum, ← (Fin.consEquiv fun _ => Fin (e + 2)).sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin (e + 2)).sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Finset.prod_mul_distrib,
    ← Fin.succ_zero_eq_one]
  ring

theorem secondChernDensity_chg_eq_norm_det_sq_mul {e : ℕ} (Θ : V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ)
    (J A : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ) (T : V (e + 2) → V (e + 2))
    (hT : ∀ j, T (bas _ j) = ∑ a, J a j • bas _ a)
    (hl : ∀ (x y : Fin (e + 2) → ℂ) (η η' : V (e + 2)), Θ (∑ a, x a • bas _ a) η (∑ c, y c • bas _ c) η' =
      ∑ a, ∑ c, x a * y c * Θ (bas _ a) η (bas _ c) η')
    (hr : ∀ (x y : Fin (e + 2) → ℂ) (ξ ξ' : V (e + 2)), Θ ξ (∑ a, x a • bas _ a) ξ' (∑ c, y c • bas _ c) =
      ∑ a, ∑ c, star (x a) * star (y c) * Θ ξ (bas _ a) ξ' (bas _ c)) :
    secondChernDensity e (fun a b c d => Θ (T a) (T b) (T c) (T d)) (chg J A) = ‖J.det‖ ^ 2 * secondChernDensity e Θ A := by
  have h₁ (t : Equiv.Perm (Fin (e + 2))) := alt_sum_two J
    (of fun a c => Θ (bas _ a) (T (bas _ (t 0))) (bas _ c) (T (bas _ (t 1)))) fun i a => (A * Jᴴᵀ) a (t i.succ.succ)
  have h₂ (s : Equiv.Perm (Fin (e + 2))) := alt_sum_two Jᴴᵀ
    (of fun a c => Θ (bas _ (s 0)) (bas _ a) (bas _ (s 1)) (bas _ c)) fun i a => A (s i.succ.succ) a
  have key : ∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
      (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) *
        (Θ (T (bas _ (s 0))) (T (bas _ (t 0))) (T (bas _ (s 1))) (T (bas _ (t 1))) *
          ∏ i : Fin e, chg J A (s i.succ.succ) (t i.succ.succ)) =
      ((‖J.det‖ ^ 2 : ℝ) : ℂ) * ∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
        (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) *
          (Θ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) *
            ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ)) := by
    have hd : ((‖J.det‖ ^ 2 : ℝ) : ℂ) = J.det * Jᴴᵀ.det := by
      rw [det_transpose, det_conjTranspose, Complex.star_def, Complex.ofReal_pow, Complex.mul_conj']
    calc _ = ∑ t : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign t : ℤ) : ℂ) * (J.det *
          ∑ s : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
            (Θ (bas _ (s 0)) (T (bas _ (t 0))) (bas _ (s 1)) (T (bas _ (t 1))) *
              ∏ i : Fin e, (A * Jᴴᵀ) (s i.succ.succ) (t i.succ.succ))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          refine Eq.trans ?_ (congrArg _ (h₁ t))
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hT (s 0), hT (s 1), hl, chg, Matrix.mul_assoc]
          simp only [mul_apply (M := Jᵀ), transpose_apply, of_apply]
          push_cast
          ring
      _ = J.det * ∑ s : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign s : ℤ) : ℂ) * (Jᴴᵀ.det *
          ∑ t : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign t : ℤ) : ℂ) *
            (Θ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) *
              ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ))) := by
          have h₃ (s : Equiv.Perm (Fin (e + 2))) := (h₂ s).symm
          simp only [of_apply] at h₃
          simp only [h₃, Finset.mul_sum (Finset.univ : Finset (Equiv.Perm (Fin (e + 2))))]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          rw [hT (t 0), hT (t 1), hr]
          simp only [mul_apply, transpose_apply, conjTranspose_apply, mul_comm (A _ _)]
          ring
      _ = _ := by
          simp only [hd, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
          push_cast
          ring
  rw [secondChernDensity, secondChernDensity, key, Complex.re_ofReal_mul]
  ring

section Curv

variable {n r : ℕ} {H K : V n → Matrix (Fin r) (Fin r) ℂ} {z : V n}

theorem chTwo_trace (H : V n → Matrix (Fin r) (Fin r) ℂ) (z a b c d : V n) : chTwo H z a b c d = kappa ^ 2 / 2 *
    ((curv H z a b * curv H z c d).trace + (curv H z c d * curv H z a b).trace -
      (curv H z a d * curv H z c b).trace - (curv H z c b * curv H z a d).trace) := by
  simp only [chTwo, HermFrame.wedge, trace, diag_apply, mul_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem curv_sum_left (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (x : Fin n → ℂ) (u : Fin n → V n) (η : V n) :
    curv H z (∑ a, x a • u a) η = ∑ a, x a • curv H z (u a) η := by
  have hs := isSesq_curv h hu
  let L : V n →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ :=
    ⟨⟨fun ξ => curv H z ξ η, fun _ _ => hs.add_left _ _ _⟩, fun _ _ => hs.smul_left _ _ _⟩
  change L _ = ∑ a, x a • L (u a)
  simp only [map_sum, map_smul]

theorem curv_sum_right (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (x : Fin n → ℂ) (u : Fin n → V n) (ξ : V n) :
    curv H z ξ (∑ a, x a • u a) = ∑ a, star (x a) • curv H z ξ (u a) := by
  have hs := isSesq_curv h hu
  let L : V n →ₛₗ[starRingEnd ℂ] Matrix (Fin r) (Fin r) ℂ :=
    ⟨⟨fun η => curv H z ξ η, fun _ _ => hs.add_right _ _ _⟩, fun _ _ => hs.smul_right _ _ _⟩
  change L _ = ∑ a, (starRingEnd ℂ) (x a) • L (u a)
  simp only [map_sum, map_smulₛₗ]

theorem trace_sum_mul_sum (x y : Fin n → ℂ) (M N : Fin n → Matrix (Fin r) (Fin r) ℂ) :
    ((∑ a, x a • M a) * ∑ c, y c • N c).trace = ∑ a, ∑ c, x a * y c * (M a * N c).trace := by
  rw [Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem chTwo_sum_left (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (x y : Fin n → ℂ) (u : Fin n → V n)
    (η η' : V n) : chTwo H z (∑ a, x a • u a) η (∑ c, y c • u c) η' =
      ∑ a, ∑ c, x a * y c * chTwo H z (u a) η (u c) η' := by
  rw [chTwo_trace, trace_mul_comm (curv H z _ η'), trace_mul_comm (curv H z (∑ c, y c • u c) η)]
  simp only [curv_sum_left h hu, trace_sum_mul_sum]
  simp only [chTwo_trace, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [trace_mul_comm (curv H z (u c) η'), trace_mul_comm (curv H z (u c) η)]
  ring

theorem chTwo_sum_right (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (x y : Fin n → ℂ) (u : Fin n → V n)
    (ξ ξ' : V n) : chTwo H z ξ (∑ a, x a • u a) ξ' (∑ c, y c • u c) =
      ∑ a, ∑ c, star (x a) * star (y c) * chTwo H z ξ (u a) ξ' (u c) := by
  rw [chTwo_trace, trace_mul_comm (curv H z ξ' (∑ c, y c • u c)), trace_mul_comm (curv H z ξ (∑ c, y c • u c))]
  simp only [curv_sum_right h hu, trace_sum_mul_sum]
  simp only [chTwo_trace, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [trace_mul_comm (curv H z ξ' (u c)), trace_mul_comm (curv H z ξ (u c))]
  ring

theorem chTwo_conj {A : Matrix (Fin r) (Fin r) ℂ} (hA : IsUnit A.det)
    (h : ∀ ξ η, curv H z ξ η = A⁻¹ * curv K z ξ η * A) : chTwo H z = chTwo K z := by
  have e (M N : Matrix (Fin r) (Fin r) ℂ) : (A⁻¹ * M * A * (A⁻¹ * N * A)).trace = (M * N).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hA, trace_mul_comm,
      Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hA]
  ext a b c d
  simp only [chTwo_trace, h, e]

theorem continuousAt_chTwo (h : MContDiffAt ∞ H z) (hu : IsUnit (H z).det) (a b c d : V n) :
    ContinuousAt (fun w => chTwo H w a b c d) z := by
  have hc (ξ η : V n) (i j : Fin r) : ContinuousAt (fun w => curv H w ξ η i j) z :=
    (h.curv (j := 0) hu (by norm_cast) ξ η i j).continuousAt
  simp only [chTwo, HermFrame.wedge]
  refine continuousAt_const.mul (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_)
  exact ((((hc ..).mul (hc ..)).add ((hc ..).mul (hc ..))).sub ((hc ..).mul (hc ..))).sub ((hc ..).mul (hc ..))

end Curv

section Main

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {E : X.Modules} {r D : ℕ}
  {h : Met p σ E r}

theorem chTwo_frame (H : h.IsCInf) (c : AlgChart p σ D) (a a' : Chart E r) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (ha : y ∈ ptsIn p σ a.U) (ha' : y ∈ ptsIn p σ a'.U) :
    chTwo (fun u => h.G a' (c.e.symm u)) (c.e y) = chTwo (fun u => h.G a (c.e.symm u)) (c.e y) := by
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (a'.U ⊓ a.U))
  have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha', ha⟩))
  have hA (i j : Fin r) : DifferentiableOn ℂ (fun v => Chart.tr p σ a a' (c.e.symm v) i j)
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (a'.U ⊓ a.U)) := c.holo _ _
  have hAu : IsUnit (Chart.tr p σ a a' (c.e.symm (c.e y))).det := by
    rw [c.e.left_inv hy]
    exact (isUnit_iff_isUnit_det _).1 (Chart.isUnit_tr a a' ha ha')
  have hu : IsUnit (h.G a (c.e.symm (c.e y))).det := by
    rw [c.e.left_inv hy]
    exact (h.posDef a y ha).det_pos.ne'.isUnit
  refine chTwo_conj hAu fun ξ η => ?_
  rw [← curv_changeFrame (A := fun v => Chart.tr p σ a a' (c.e.symm v))
    (((H a y ha).mContDiffAt c hy).of_le (by norm_cast)) hu
    (fun i j => (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (hA i j)).contDiffAt hm).of_le
      (by norm_cast)).restrict_scalars ℝ) hAu
    (eventually_of_mem hm fun v hv η => by
      ext i j
      rw [mdbar_apply, GlobalTheory.dbar_eq_zero ((hA i j).differentiableAt (ho.mem_nhds hv))]
      rfl)]
  exact curv_congr (eventually_of_mem hm fun v hv => h.trans a a' _ (mem_ptsIn_inf.1 hv.2).2) ξ η

variable {L : LB X} {φ : Weight p σ L} {e : ℕ}

theorem ch2Dens_eq (H : h.IsCInf) (c : AlgChart p σ (e + 2)) (a : Chart E r) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (ha : y ∈ ptsIn p σ a.U) :
    secondChernDensityOfMetric h φ e c y = secondChernDensity e (chTwo (fun u => h.G a (c.e.symm u)) (c.e y)) (chernMat φ c y) := by
  rw [secondChernDensityOfMetric, chTwo_frame H c a _ hy ha (h.isVB.mem_pick y)]

theorem ch2Dens_trans (H : h.IsCInf) (hφ : φ.IsCInf) (c c' : AlgChart p σ (e + 2)) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    secondChernDensityOfMetric h φ e c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * secondChernDensityOfMetric h φ e c' y := by
  have ha := h.isVB.mem_pick y
  have ho := ChartGlue.isOpen_over c.e c'.e.open_source
  have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hd := ((H _ y ha).mContDiffAt c' hy').of_le (j := 2) (by norm_cast)
  have hu : IsUnit (h.G (h.isVB.pick y) (c'.e.symm (c'.e y))).det := by
    rw [c'.e.left_inv hy']
    exact (h.posDef _ y ha).det_pos.ne'.isUnit
  have hl (j : Fin (e + 2)) : fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (bas _ j) =
      ∑ b, MixDens.transMat c c' y b j • bas _ b := by
    ext i
    simp [MixDens.transMat, bas, Finset.sum_apply, Pi.single_apply]
  have hc (ξ η : V (e + 2)) : curv (fun u => h.G (h.isVB.pick y) (c.e.symm u)) (c.e y) ξ η =
      curv (fun u => h.G (h.isVB.pick y) (c'.e.symm u)) (c'.e y) (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) ξ)
        (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) η) := by
    rw [curv_congr (H' := fun v => h.G (h.isVB.pick y) (c'.e.symm ((c'.e ∘ c.e.symm) v)))
        (eventually_of_mem hm fun v hv => by simp only [Function.comp_apply, c'.e.left_inv hv.2]),
      curv_comp_holo (H := fun v => h.G (h.isVB.pick y) (c'.e.symm v)) (e₂ ▸ hd) (e₂ ▸ hu)
        (contDiffAt_euclidean.2 fun i => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
          (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)), e₂]
  have hm : chernMat φ c y = chg (MixDens.transMat c c' y) (chernMat φ c' y) :=
    (MixDens.chernMat_isForm k X p σ (e + 2) L φ hφ).1 c c' y hy hy'
  have ht := secondChernDensity_chg_eq_norm_det_sq_mul (chTwo (fun u => h.G (h.isVB.pick y) (c'.e.symm u)) (c'.e y)) (MixDens.transMat c c' y)
    (chernMat φ c' y) (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y)) hl (fun x y => chTwo_sum_left hd hu x y _)
    (fun x y => chTwo_sum_right hd hu x y _)
  rw [secondChernDensityOfMetric, secondChernDensityOfMetric, ← MixDens.det_transMat, hm, ← ht]
  refine congrArg (secondChernDensity e · _) ?_
  funext a b c d
  rw [chTwo_trace, chTwo_trace, hc, hc, hc, hc]

theorem continuousOn_ch2Dens (H : h.IsCInf) (hφ : φ.IsCInf) (c : AlgChart p σ (e + 2)) :
    ContinuousOn (fun v => secondChernDensityOfMetric h φ e c (c.e.symm v)) c.e.target := by
  intro v hv
  have ha := h.isVB.mem_pick (c.e.symm v)
  have hm := (ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) _)).mem_nhds (show v ∈ _ from ⟨hv, ha⟩)
  have hK : MContDiffAt ∞ (fun u => h.G (h.isVB.pick (c.e.symm v)) (c.e.symm u)) v := by
    have := (H _ _ ha).mContDiffAt c (c.e.map_target hv)
    rwa [c.e.right_inv hv] at this
  have hA : ContinuousAt (fun v => chernMat φ c (c.e.symm v)) v :=
    ((MixDens.chernMat_isForm k X p σ (e + 2) L φ hφ).2.1 c).continuousAt (c.e.open_target.mem_nhds hv)
  have hc : ContinuousAt (fun w => secondChernDensity e (chTwo (fun u => h.G (h.isVB.pick (c.e.symm v)) (c.e.symm u)) w)
      (chernMat φ c (c.e.symm w))) v := by
    unfold secondChernDensity
    refine (Complex.continuous_re.continuousAt.comp ?_).neg.div_const _
    refine tendsto_finset_sum _ fun s _ => tendsto_finset_sum _ fun t _ => ?_
    exact continuousAt_const.mul ((continuousAt_chTwo hK (h.posDef _ _ ha).det_pos.ne'.isUnit _ _ _ _).mul
      (tendsto_finset_prod _ fun i _ => continuousAt_pi.1 (continuousAt_pi.1 hA _) _))
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hm] with w hw
  rw [ch2Dens_eq H c _ (c.e.map_target hw.1) hw.2, c.e.right_inv hw.1]

end Main

theorem isDens_ch2Dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) (h : Met p σ E r) (L : LB X) (φ : Weight p σ L) (e : ℕ), h.IsCInf → φ.IsCInf → IsDens (secondChernDensityOfMetric h φ e) ∧ ∀ (c : AlgChart p σ (e + 2)) (cE : Chart E r), ∀ y ∈ c.e.source, y ∈ ptsIn p σ cE.U → secondChernDensityOfMetric h φ e c y = secondChernDensity e (chTwo (fun u => h.G cE (c.e.symm u)) (c.e y)) (chernMat φ c y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ H hφ =>
    ⟨⟨fun c c' _ hy hy' => ch2Dens_trans H hφ c c' hy hy', continuousOn_ch2Dens H hφ⟩,
      fun c a _ hy ha => ch2Dens_eq H c a hy ha⟩

end GlobalTheory.ArchLim.ChTwoDens
