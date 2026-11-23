import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BesselHermitian

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

def SSh (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r}

def Shh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (p.1, conjM (Matrix.of p.1)⁻¹ (invM p.2))

def Ivh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (invM (Shh p).1, (Shh p).2)

theorem bh_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem bh_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]; exact h.conc

theorem bh_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ)

theorem bh_meas_inv : Measurable (invM (k := k) (r := r)) := by
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

theorem bh_cont_mul : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

theorem bh_meas_conj (a : Mat k r) : Measurable (conjM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x * a⁻¹
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem bh_meas_Shh : Measurable (Shh (k := k) (r := r)) := by
  refine measurable_fst.prodMk ?_
  change Measurable fun p : Mt k r × Mt k r => mulM (mulM (invM p.1, invM p.2), invM (invM p.1))
  exact bh_cont_mul.measurable.comp ((bh_cont_mul.measurable.comp
    ((bh_meas_inv.comp measurable_fst).prodMk (bh_meas_inv.comp measurable_snd))).prodMk
    (bh_meas_inv.comp (bh_meas_inv.comp measurable_fst)))

section meas

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

theorem ae_SSh : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ SSh D.z := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  exact bh_ae_prod_and (bh_ae_mem D.haarW) (bh_ae_mem D.haarN)

theorem mp_Shh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Shh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  refine ⟨bh_meas_Shh, ?_⟩
  ext s hs
  rw [Measure.map_apply bh_meas_Shh hs, Measure.prod_apply (bh_meas_Shh hs), Measure.prod_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [bh_ae_mem D.haarW] with h hh
  have hi : (Matrix.of h : Mat k r)⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hm : Measurable fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n) :=
    (bh_meas_conj _).comp bh_meas_inv
  have e : Prod.mk h ⁻¹' (Shh ⁻¹' s) = (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) ⁻¹'
      (Prod.mk h ⁻¹' s) := rfl
  have hmap : D.μN.map (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) = D.μN := by
    have e2 : (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) =
        conjM (Matrix.of h : Mat k r)⁻¹ ∘ invM := rfl
    rw [e2, ← Measure.map_map (bh_meas_conj _) bh_meas_inv, hInv k r _ _ (hCN k r) D.haarN]
    exact hCI _ (Or.inl hi)
  rw [e, ← Measure.map_apply hm (measurable_prodMk_left hs), hmap]

theorem mp_Ivh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Ivh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  have h1 : MeasurePreserving (invM (k := k) (r := r)) D.μW D.μW :=
    ⟨bh_meas_inv, hInv k r _ _ (hCW k r D.z) D.haarW⟩
  exact (h1.prod (MeasurePreserving.id D.μN)).comp (mp_Shh D hCI hInv hCW hCN)

end meas

section key

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
  (D : RealPlaceData k r Wp Wp) (X : SigData k r)

theorem inner_move_sig (hCG : ClosedG) {g : Mat k r} (hg : g ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ g a, b⟫_ℂ = ⟪a, X.σ g⁻¹ b⟫_ℂ := by
  have hgi : g⁻¹ ∈ GV k r := (hCG k r).inv_mem _ hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g ((hCG k r).unit _ hg)
  let e : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g).toLinearMap, fun v => X.rep.2.1 g hg v⟩
  have hb : X.σ g (X.σ g⁻¹ b) = b := by
    have := X.rep.1.2 g hg g⁻¹ hgi
    rw [hgg, X.rep.1.1] at this
    have h2 := congrArg (fun L : X.Hs →L[ℂ] X.Hs => L b) this
    simpa using h2.symm
  calc ⟪X.σ g a, b⟫_ℂ = ⟪e a, e (X.σ g⁻¹ b)⟫_ℂ := by
        simp only [e]; exact congrArg _ hb.symm
    _ = ⟪a, X.σ g⁻¹ b⟫_ℂ := e.inner_map_map a _

theorem inner_move_pi (hCW : ClosedW) {h : Mat k r} (hh : h ∈ UWset k r D.z) (a b : Wp) :
    ⟪D.π h a, b⟫_ℂ = ⟪a, D.π h⁻¹ b⟫_ℂ := by
  have hhi : h⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hhh : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h ((hCW k r D.z).unit _ hh)
  let e : Wp →ₗᵢ[ℂ] Wp := ⟨(D.π h).toLinearMap, fun v => D.π_unitary h hh v⟩
  have hb : D.π h (D.π h⁻¹ b) = b := by
    have := D.π_rep.2 h hh h⁻¹ hhi
    rw [hhh, D.π_rep.1] at this
    have h2 := congrArg (fun L : Wp →L[ℂ] Wp => L b) this
    simpa using h2.symm
  calc ⟪D.π h a, b⟫_ℂ = ⟪e a, e (D.π h⁻¹ b)⟫_ℂ := by
        simp only [e]; exact congrArg _ hb.symm
    _ = ⟪a, D.π h⁻¹ b⟫_ℂ := e.inner_map_map a _

theorem psiD_conj' (hUN : UWNormal) {h m : Mat k r} (hh : h ∈ UWset k r D.z) (hm : m ∈ Nset k r) :
    psiD D (h * m * h⁻¹) = psiD D m := by
  unfold psiD psi; rw [(hUN k r D.z D.z_mem h hh m hm).2]

theorem psiD_inv' (hEA : EllAdd) (hCN : ClosedN) {m : Mat k r} (hm : m ∈ Nset k r) :
    psiD D m⁻¹ = star (psiD D m) := by
  have hmi : m⁻¹ ∈ Nset k r := (hCN k r).inv_mem _ hm
  have h1 : (1 : Mat k r) ∈ Nset k r := (hCN k r).one_mem
  have hm1 : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m ((hCN k r).unit _ hm)
  have e0 : ell k r D.z 1 = 0 := by
    have := hEA k r D.z D.z_mem 1 h1 1 h1
    rw [Matrix.one_mul] at this
    linear_combination -this
  have e1 : ell k r D.z m⁻¹ = -ell k r D.z m := by
    have := hEA k r D.z D.z_mem m⁻¹ hmi m hm
    rw [hm1, e0] at this
    linear_combination -this
  unfold psiD psi
  rw [e1, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  rw [mul_neg, Complex.neg_re, Complex.ofReal_neg]
  ring

theorem key (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal) (hEA : EllAdd)
    (u u' : X.Hs) {p : Mt k r × Mt k r} (hp : p ∈ SSh D.z) :
    beInt D X u' u (Ivh p) = ContinuousLinearMap.adjoint (beInt D X u u' p) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  obtain ⟨hH, hN⟩ := hp
  have eH : (Matrix.of (Ivh p).1 : Mat k r) = (Matrix.of p.1 : Mat k r)⁻¹ := rfl
  have eN : (Matrix.of (Ivh p).2 : Mat k r) =
      (Matrix.of p.1 : Mat k r)⁻¹ * (Matrix.of p.2 : Mat k r)⁻¹ * ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ := rfl
  simp only [beInt, eH, eN]
  generalize (Matrix.of p.1 : Mat k r) = H at hH ⊢
  generalize (Matrix.of p.2 : Mat k r) = N at hN ⊢
  have hHu : IsUnit H.det := (hCW k r D.z).unit _ hH
  have hHi : H⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hH
  have hNi : N⁻¹ ∈ Nset k r := (hCN k r).inv_mem _ hN
  have hHH : H⁻¹⁻¹ = H := Matrix.nonsing_inv_nonsing_inv H hHu
  have hNH : N * H ∈ GV k r := (hCG k r).mul_mem _ hN.1 _ hH.1
  have hs : H⁻¹ * N⁻¹ * H⁻¹⁻¹ * H⁻¹ = (N * H)⁻¹ := by
    rw [hHH, Matrix.mul_assoc, Matrix.mul_nonsing_inv H hHu, Matrix.mul_one, Matrix.mul_inv_rev]
  have hps : psiD D (H⁻¹ * N⁻¹ * H⁻¹⁻¹) = star (psiD D N) := by
    rw [psiD_conj' D hUN hHi hNi, psiD_inv' D hEA hCN hN]
  have hmc : starRingEnd ℂ (mc X u' u (N * H)⁻¹) = mc X u u' (N * H) := by
    unfold mc
    rw [inner_conj_symm, inner_move_sig X hCG ((hCG k r).inv_mem _ hNH),
      Matrix.nonsing_inv_nonsing_inv _ ((hCG k r).unit _ hNH)]
  rw [hs, hps, hHH]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, star_star]
  rw [inner_move_pi D hCW hH x y, map_mul, hmc]
  rfl

end key

section main

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
  (D : RealPlaceData k r Wp Wp) (X : SigData k r)

theorem inner_int {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → Wp →L[ℂ] Wp}
    (hf : Integrable f μ) (a b : Wp) : ⟪a, (∫ p, f p ∂μ) b⟫_ℂ = ∫ p, ⟪a, f p b⟫_ℂ ∂μ := by
  have := ((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ Wp b)).integral_comp_comm hf
  simpa [innerSL_apply_apply] using this.symm

theorem int_adj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → Wp →L[ℂ] Wp}
    (hf : Integrable f μ) : Integrable (fun p => ContinuousLinearMap.adjoint (f p)) μ :=
  hf.congr' ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).norm_map _).symm)

theorem int_swap (hCI : ConjInv D) (hInv : HaarInv) (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN)
    (hUN : UWNormal) (hEA : EllAdd) (u u' : X.Hs) (hI : Integrable (beInt D X u u') (D.μW.prod D.μN)) :
    Integrable (beInt D X u' u) (D.μW.prod D.μN) := by
  have hmp := mp_Ivh D hCI hInv hCW hCN
  have h1 : Integrable (beInt D X u u' ∘ Ivh) (D.μW.prod D.μN) := by
    apply Integrable.comp_measurable _ hmp.measurable
    rw [hmp.map_eq]; exact hI
  refine (int_adj h1).congr ?_
  filter_upwards [ae_SSh D] with p hp
  show ContinuousLinearMap.adjoint (beInt D X u u' (Ivh p)) = beInt D X u' u p
  rw [key D X hCG hCW hCN hUN hEA u' u hp, ContinuousLinearMap.adjoint_adjoint]

theorem herm_main (hCI : ConjInv D) (hInv : HaarInv) (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN)
    (hUN : UWNormal) (hEA : EllAdd) (u u' : X.Hs) (η ξ : Wp) :
    ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ := by
  unfold beOp
  by_cases hI : Integrable (beInt D X u u') (D.μW.prod D.μN)
  · have hJ := int_swap D X hCI hInv hCG hCW hCN hUN hEA u u' hI
    have hmp := mp_Ivh D hCI hInv hCW hCN
    have hA := int_adj hI
    have e1 : ∫ p, beInt D X u' u p ∂(D.μW.prod D.μN) =
        ∫ p, ContinuousLinearMap.adjoint (beInt D X u u' p) ∂(D.μW.prod D.μN) := by
      have e2 : ∫ p, beInt D X u' u p ∂(D.μW.prod D.μN) = ∫ p, beInt D X u' u (Ivh p) ∂(D.μW.prod D.μN) := by
        conv_lhs => rw [← hmp.map_eq]
        exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hJ.aestronglyMeasurable)
      rw [e2]
      refine integral_congr_ae ?_
      filter_upwards [ae_SSh D] with p hp
      exact key D X hCG hCW hCN hUN hEA u u' hp
    rw [e1]
    calc ⟪ξ, (∫ p, beInt D X u u' p ∂(D.μW.prod D.μN)) η⟫_ℂ
        = ∫ p, ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN) := inner_int hI ξ η
      _ = starRingEnd ℂ (starRingEnd ℂ (∫ p, ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN))) :=
          (Complex.conj_conj _).symm
      _ = starRingEnd ℂ (∫ p, starRingEnd ℂ ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN)) := by
          rw [integral_conj]
      _ = starRingEnd ℂ (∫ p, ⟪η, ContinuousLinearMap.adjoint (beInt D X u u' p) ξ⟫_ℂ ∂(D.μW.prod D.μN)) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show starRingEnd ℂ ⟪ξ, beInt D X u u' p η⟫_ℂ = ⟪η, ContinuousLinearMap.adjoint (beInt D X u u' p) ξ⟫_ℂ
          rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
      _ = starRingEnd ℂ ⟪η, (∫ p, ContinuousLinearMap.adjoint (beInt D X u u' p) ∂(D.μW.prod D.μN)) ξ⟫_ℂ := by
          rw [inner_int hA η ξ]
      _ = _ := inner_conj_symm _ _
  · have hJ : ¬ Integrable (beInt D X u' u) (D.μW.prod D.μN) := fun h =>
      hI (int_swap D X hCI hInv hCG hCW hCN hUN hEA u' u h)
    rw [integral_undef hI, integral_undef hJ]
    simp

end main

end ReciprocityTheory.ChartRestriction.DS.Mult1.BesselHermitian

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBeHerm (h : UnitaryGroupStructuralFacts) : StBeHerm := by
  intro k r Wp _ _ _ D X _ _ u _ u' _ η ξ
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨hB2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUN, hEA, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIA, -, -, -, -, hInv, -, hCG, hCN, hCW, -⟩ := hB2
  exact BesselHermitian.herm_main D X (hCIA k r Wp Wp D) hInv hCG hCW hCN hUN hEA u u' η ξ

end ReciprocityTheory.ChartRestriction.DS.Mult1
