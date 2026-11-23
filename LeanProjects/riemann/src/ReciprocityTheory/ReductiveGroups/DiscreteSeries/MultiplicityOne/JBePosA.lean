import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

def sP (p : Mt k r × Mt k r) : Mat k r := Matrix.of p.2 * Matrix.of p.1

def SS (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r}

def Lq (q p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (lmulM (Matrix.of q.1) p.1, lmulM (Matrix.of q.2) (conjM (Matrix.of q.1) p.2))

def Sh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (p.1, conjM (Matrix.of p.1)⁻¹ (invM p.2))

def Iv (p : Mt k r × Mt k r) : Mt k r × Mt k r := (invM (Sh p).1, (Sh p).2)

def Tm (p : Mt k r × (Mt k r × Mt k r)) : Mt k r × (Mt k r × Mt k r) :=
  (mulM (p.1, mulM (p.2.2, p.2.1)), p.2)

theorem bp_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem bp_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]; exact h.conc

theorem bp_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ)

theorem bp_meas_inv : Measurable (invM (k := k) (r := r)) := by
  have hc : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) := continuous_id
  have h1 : Measurable (fun g : Mt k r => ((Matrix.of g : Mat k r).det)⁻¹) :=
    (hc.matrix_det).measurable.inv
  have h2 : Continuous (fun g : Mt k r => Matrix.of.symm (Matrix.of g : Mat k r).adjugate) :=
    hc.matrix_adjugate
  have h3 : Measurable (fun g : Mt k r =>
      ((Matrix.of g : Mat k r).det)⁻¹ • Matrix.of.symm (Matrix.of g : Mat k r).adjugate) :=
    h1.smul h2.measurable
  convert h3 using 1
  funext g
  simp only [invM]
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

theorem bp_cont_mul : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

theorem bp_cont_gN : Continuous (fun g : Mat k r => gN g) := by
  unfold gN; fun_prop

theorem det_unit_G {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (ConjugateNormInequalities.UH_left_inv k r hg)

theorem inv_mul_G {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (det_unit_G hg)

theorem mul_inv_G {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (det_unit_G hg)

theorem sP_mem {z : Fin (2 * r + k + 1) → ℂ} (hCG : ClosedG) {p : Mt k r × Mt k r} (hp : p ∈ SS z) :
    sP p ∈ GV k r :=
  (hCG k r).mul_mem _ hp.2.1 _ hp.1.1

theorem sP_Lq {z : Fin (2 * r + k + 1) → ℂ} {q : Mt k r × Mt k r} (hq : q ∈ SS z) (p : Mt k r × Mt k r) :
    sP (Lq q p) = sP q * sP p := by
  have h1 := inv_mul_G hq.1.1
  show (Matrix.of q.2 : Mat k r) * ((Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹) *
      ((Matrix.of q.1 : Mat k r) * Matrix.of p.1) = Matrix.of q.2 * Matrix.of q.1 * (Matrix.of p.2 * Matrix.of p.1)
  simp only [mul_assoc]
  rw [← mul_assoc ((Matrix.of q.1 : Mat k r)⁻¹), h1, one_mul]

theorem Lq_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal)
    {q p : Mt k r × Mt k r} (hq : q ∈ SS z) (hp : p ∈ SS z) : Lq q p ∈ SS z :=
  ⟨(hCW k r z).mul_mem _ hq.1 _ hp.1, (hCN k r).mul_mem _ hq.2 _ (hUN k r z hz _ hq.1 _ hp.2).1⟩

theorem sP_Iv {z : Fin (2 * r + k + 1) → ℂ} {p : Mt k r × Mt k r} (hp : p ∈ SS z) : sP (Iv p) = (sP p)⁻¹ := by
  have hu := det_unit_G hp.1.1
  have h1 := mul_inv_G hp.1.1
  show (Matrix.of p.1 : Mat k r)⁻¹ * (Matrix.of p.2 : Mat k r)⁻¹ * ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ *
      (Matrix.of p.1 : Mat k r)⁻¹ = ((Matrix.of p.2 : Mat k r) * Matrix.of p.1)⁻¹
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, mul_assoc, h1, mul_one]

theorem Iv_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal)
    {p : Mt k r × Mt k r} (hp : p ∈ SS z) : Iv p ∈ SS z := by
  have hi : (Matrix.of p.1 : Mat k r)⁻¹ ∈ UWset k r z := (hCW k r z).inv_mem _ hp.1
  refine ⟨hi, ?_⟩
  have h2 := (hUN k r z hz _ hi _ ((hCN k r).inv_mem _ hp.2)).1
  have e : ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ = Matrix.of p.1 := Matrix.nonsing_inv_nonsing_inv _ (det_unit_G hp.1.1)
  show (Matrix.of p.1 : Mat k r)⁻¹ * (Matrix.of p.2 : Mat k r)⁻¹ * ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ ∈ Nset k r
  exact h2

theorem meas_lmul (a : Mat k r) : Measurable (lmulM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x
  exact continuous_const.matrix_mul continuous_id

theorem meas_conj (a : Mat k r) : Measurable (conjM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x * a⁻¹
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem meas_rmul (a : Mat k r) : Measurable (rmulF a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => x * a
  exact continuous_id.matrix_mul continuous_const

theorem meas_sP : Measurable (fun p : Mt k r × Mt k r => mulM (p.2, p.1)) :=
  bp_cont_mul.measurable.comp (measurable_snd.prodMk measurable_fst)

theorem cont_sP : Continuous (fun p : Mt k r × Mt k r => (sP p : Mat k r)) := by
  unfold sP; exact (continuous_snd (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_fst

theorem meas_Sh : Measurable (Sh (k := k) (r := r)) := by
  refine measurable_fst.prodMk ?_
  change Measurable fun p : Mt k r × Mt k r => mulM (mulM (invM p.1, invM p.2), invM (invM p.1))
  exact bp_cont_mul.measurable.comp ((bp_cont_mul.measurable.comp
    ((bp_meas_inv.comp measurable_fst).prodMk (bp_meas_inv.comp measurable_snd))).prodMk
    (bp_meas_inv.comp (bp_meas_inv.comp measurable_fst)))

theorem meas_Tm : Measurable (Tm (k := k) (r := r)) :=
  (bp_cont_mul.measurable.comp (measurable_fst.prodMk (meas_sP.comp measurable_snd))).prodMk measurable_snd

theorem isClosed_SS (hCW : ClosedW) (hCN : ClosedN) (z : Fin (2 * r + k + 1) → ℂ) :
    IsClosed (SS (k := k) (r := r) z) :=
  ((hCW k r z).closed.preimage continuous_fst).inter ((hCN k r).closed.preimage continuous_snd)

theorem aesm_of_contOn {α E : Type*} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] {μ : Measure α}
    {f : α → E} {s : Set α} (hs : IsClosed s) (hf : ContinuousOn f s) (h : ∀ᵐ x ∂μ, x ∈ s) :
    AEStronglyMeasurable f μ := by
  have := hf.aestronglyMeasurable (μ := μ) hs.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem h] at this

section meas

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

theorem ae_SS : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ SS D.z := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  exact bp_ae_prod_and (bp_ae_mem D.haarW) (bp_ae_mem D.haarN)

theorem mp_Lq (hCI : ConjInv D) {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) :
    MeasurePreserving (Lq q) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have h1 : MeasurePreserving (lmulM (k := k) (r := r) (Matrix.of q.1)) D.μW D.μW :=
    ⟨meas_lmul _, D.haarW.left _ hq.1⟩
  have h2 : MeasurePreserving (conjM (k := k) (r := r) (Matrix.of q.1)) D.μN D.μN :=
    ⟨meas_conj _, hCI _ (Or.inl hq.1)⟩
  have h3 : MeasurePreserving (lmulM (k := k) (r := r) (Matrix.of q.2)) D.μN D.μN :=
    ⟨meas_lmul _, D.haarN.left _ hq.2⟩
  exact h1.prod (h3.comp h2)

theorem mp_Sh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Sh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  refine ⟨meas_Sh, ?_⟩
  ext s hs
  rw [Measure.map_apply meas_Sh hs, Measure.prod_apply (meas_Sh hs), Measure.prod_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [bp_ae_mem D.haarW] with h hh
  have hi : (Matrix.of h : Mat k r)⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hm : Measurable fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n) :=
    (meas_conj _).comp bp_meas_inv
  have e : Prod.mk h ⁻¹' (Sh ⁻¹' s) = (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) ⁻¹'
      (Prod.mk h ⁻¹' s) := rfl
  have hmap : D.μN.map (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) = D.μN := by
    have e2 : (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) =
        conjM (Matrix.of h : Mat k r)⁻¹ ∘ invM := rfl
    rw [e2, ← Measure.map_map (meas_conj _) bp_meas_inv, hInv k r _ _ (hCN k r) D.haarN]
    exact hCI _ (Or.inl hi)
  rw [e, ← Measure.map_apply hm (measurable_prodMk_left hs), hmap]

theorem mp_Iv (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Iv (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have h1 : MeasurePreserving (invM (k := k) (r := r)) D.μW D.μW :=
    ⟨bp_meas_inv, hInv k r _ _ (hCW k r D.z) D.haarW⟩
  exact (h1.prod (MeasurePreserving.id D.μN)).comp (mp_Sh D hCI hInv hCW hCN)

theorem mp_Tm (hCG : ClosedG) :
    MeasurePreserving (Tm (k := k) (r := r)) (D.μG.prod (D.μW.prod D.μN)) (D.μG.prod (D.μW.prod D.μN)) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have := bp_sf D.haarG
  refine ⟨meas_Tm, ?_⟩
  ext s hs
  rw [Measure.map_apply meas_Tm hs, Measure.prod_apply_symm (meas_Tm hs), Measure.prod_apply_symm hs]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_SS D] with q hq
  have e : (fun x : Mt k r => (x, q)) ⁻¹' (Tm ⁻¹' s) = rmulF (sP q) ⁻¹' ((fun x : Mt k r => (x, q)) ⁻¹' s) := rfl
  rw [e, ← Measure.map_apply (meas_rmul _) (measurable_prodMk_right hs), D.haarG.right _ (sP_mem hCG hq)]

end meas

section pi

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

def PiO (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp := psiD D (Matrix.of p.2) • D.π (Matrix.of p.1)

theorem norm_psiD (m : Mat k r) : ‖psiD D m‖ = 1 := by
  unfold psiD psi; exact Complex.norm_exp_I_mul_ofReal _

theorem psiD_mul (hEA : EllAdd) {m m' : Mat k r} (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) :
    psiD D (m * m') = psiD D m * psiD D m' := by
  unfold psiD psi
  rw [hEA k r D.z D.z_mem m hm m' hm', mul_add, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem psiD_conj (hUN : UWNormal) {h m : Mat k r} (hh : h ∈ UWset k r D.z) (hm : m ∈ Nset k r) :
    psiD D (h * m * h⁻¹) = psiD D m := by
  unfold psiD psi; rw [(hUN k r D.z D.z_mem h hh m hm).2]

theorem inner_pi {h : Mat k r} (hh : h ∈ UWset k r D.z) (a b : Wp) : ⟪D.π h a, D.π h b⟫_ℂ = ⟪a, b⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨(D.π h).toLinearMap, fun v => D.π_unitary h hh v⟩ a b

theorem inner_PiO {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) (a b : Wp) : ⟪PiO D q a, PiO D q b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [PiO, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, inner_pi D hq.1]
  have h2 : psiD D (Matrix.of q.2) * starRingEnd ℂ (psiD D (Matrix.of q.2)) = 1 := by
    rw [RCLike.mul_conj, norm_psiD]; simp
  rw [← mul_assoc, h2, one_mul]

theorem norm_PiO {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) (a : Wp) : ‖PiO D q a‖ = ‖a‖ := by
  simp only [PiO, ContinuousLinearMap.smul_apply, norm_smul, norm_psiD, D.π_unitary _ hq.1, one_mul]

theorem PiO_Lq (hEA : EllAdd) (hUN : UWNormal) {q p : Mt k r × Mt k r} (hq : q ∈ SS D.z) (hp : p ∈ SS D.z)
    (a : Wp) : PiO D (Lq q p) a = PiO D q (PiO D p a) := by
  have h1 : (Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹ ∈ Nset k r :=
    (hUN k r D.z D.z_mem _ hq.1 _ hp.2).1
  have e1 : psiD D (Matrix.of (Lq q p).2) = psiD D (Matrix.of q.2) * psiD D (Matrix.of p.2) := by
    show psiD D ((Matrix.of q.2 : Mat k r) * ((Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹)) = _
    rw [psiD_mul D hEA hq.2 h1, psiD_conj D hUN hq.1 hp.2]
  have e2 : D.π (Matrix.of (Lq q p).1) = (D.π (Matrix.of q.1)).comp (D.π (Matrix.of p.1)) :=
    D.π_rep.2 _ hq.1 _ hp.1
  simp only [PiO, ContinuousLinearMap.smul_apply, e1, e2, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm]

theorem cont_ell (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dif_pos]
    fun_prop
  · simp only [h, dif_neg, not_false_eq_true, mulVec, dotProduct]
    fun_prop

theorem cont_psiD : Continuous (psiD D) := by
  unfold psiD psi
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (cont_ell _)))))

theorem contOn_PiO (a : Wp) : ContinuousOn (fun p : Mt k r × Mt k r => PiO D p a) (SS D.z) := by
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => D.π (Matrix.of p.1) a) (SS D.z) := by
    have h0 : ContinuousOn (fun m : Mat k r => D.π m a) (UWset k r D.z) :=
      D.π_cont.clm_apply continuousOn_const
    exact h0.comp continuous_fst.continuousOn fun p hp => hp.1
  have h2 : Continuous fun p : Mt k r × Mt k r => psiD D (Matrix.of p.2) := (cont_psiD D).comp continuous_snd
  exact h2.continuousOn.smul h1

end pi

end ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity
