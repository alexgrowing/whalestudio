import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.LabApply

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB

variable {k r : ℕ}

def Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : SS k r :=
  ((gb γ p.2.1, gb γ p.2.2), (gb γ p.1.1, gb γ p.1.2))

lemma Tg_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det) (p : SS k r) :
    Tg γ (Tg γ p) = p := by
  have e : ∀ x : Mt k r, gb γ (gb γ x) = x := fun x => gbar_gbar γ hE (Matrix.of x)
  simp only [Tg, e]

lemma meas_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Measurable (Tg (k := k) (r := r) γ) :=
  (((cont_gb γ).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    ((cont_gb γ).measurable.comp (measurable_snd.comp measurable_snd))).prodMk
    (((cont_gb γ).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    ((cont_gb γ).measurable.comp (measurable_snd.comp measurable_fst)))

lemma emb_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det) :
    MeasurableEmbedding (Tg (k := k) (r := r) γ) :=
  (mEquiv (Tg γ) (Tg γ) (meas_Tg γ) (meas_Tg γ) (Tg_Tg γ hE) (Tg_Tg γ hE)).measurableEmbedding

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

lemma mp_Tg (D : RealPlaceData k r Wp Wp) (hW' : D.μW' = D.μW) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN) : MeasurePreserving (Tg γ) D.μSS D.μSS := by
  have := sfin D.haarW
  have := sfin D.haarN
  have m1 : MeasurePreserving (gb γ) D.μW D.μW := ⟨(cont_gb γ).measurable, hgW⟩
  have m2 : MeasurePreserving (gb γ) D.μN D.μN := ⟨(cont_gb γ).measurable, hgN⟩
  have m12 := m1.prod m2
  have m := (Measure.measurePreserving_swap (μ := D.μW.prod D.μN) (ν := D.μW.prod D.μN)).comp (m12.prod m12)
  unfold RealPlaceData.μSS
  rw [hW']
  exact m

lemma psi_gbar (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : Fin (2 * r + k + 1) → ℂ} {m : Mat k r}
    (hl : lam k r z (gbar k r γ m) = -lam k r z m) :
    psi k r z cStd (gbar k r γ m) = star (psi k r z cStd m) := by
  show Complex.exp (Complex.I * ((lam k r z (gbar k r γ m) : ℝ) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((lam k r z m : ℝ) : ℂ)))
  rw [hl, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

lemma rho_scalF (D : RealPlaceData k r Wp Wp) (p : SS k r) (f : Mat k r → ℂ) (g : Mat k r) :
    rho D p (scalF Wp f) g = f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π' (Matrix.of p.2.1)⁻¹) := by
  ext v
  simp [rho, scalF]

def Phi (D : RealPlaceData k r Wp Wp) (f : Mat k r → ℂ) (g : Mat k r) (p : SS k r) : Wp →L[ℂ] Wp :=
  ph D p • (f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹))

def Psi (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (f : Mat k r → ℂ) (g : Mat k r)
    (p : SS k r) : Wp →L[ℂ] Wp :=
  ph D p • (f (sgs p g) • (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹))

lemma J_phi (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (f : Mat k r → ℂ) (g : Mat k r) :
    JF D (scalF Wp f) g = ∫ p, Phi D f g p ∂D.μSS := by
  rw [JF_eq]
  congr 1
  funext p
  rw [rho_scalF, hD.π_eq]
  rfl

lemma J_th (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hE : IsUnit (embWb k r γ).det) (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (f : Mat k r → ℂ) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS := by
  rw [JF_eq, ← (mp_Tg D hD.μW_eq γ hgW hgN).integral_comp (emb_Tg γ hE)]
  refine integral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  have e3 : th k r γ (sgs (Tg γ p) g0) = sgs p g0 := by
    rw [show sgs (Tg γ p) g0 = (gbar k r γ (Matrix.of p.2.1))⁻¹ * (gbar k r γ (Matrix.of p.2.2))⁻¹ * g0 *
        gbar k r γ (Matrix.of p.1.2) * gbar k r γ (Matrix.of p.1.1) from rfl,
      th_five γ hE (gbar_unit γ hE (isUnit_of_uh hp.2.2.1.1)) (gbar_unit γ hE (isUnit_of_uh hp.2.2.2.1)) hg0,
      gbar_gbar γ hE, gbar_gbar γ hE, gbar_gbar γ hE, gbar_gbar γ hE]
    rfl
  have e4 : ph D (Tg γ p) = ph D p := by
    unfold ph
    rw [hD.z_eq]
    show psi k r D.z cStd (gbar k r γ (Matrix.of p.2.2)) * star (psi k r D.z cStd (gbar k r γ (Matrix.of p.1.2))) = _
    rw [psi_gbar γ (hlam _ hp.2.2.2), psi_gbar γ (hlam _ hp.2.1), star_star, mul_comm]
  have e5 : D.π' = D.π := hD.π_eq
  rw [rho_scalF, Function.comp_apply, e3, e4, e5]
  rfl

section trace

variable [FiniteDimensional ℂ Wp]

def trL (Y : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun X := LinearMap.trace ℂ Wp (((ContinuousLinearMap.adjoint Y).comp X : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)
  map_add' X X' := by simp [ContinuousLinearMap.comp_add]
  map_smul' c X := by simp

def trY (Y : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (trL Y)

lemma trY_apply (Y X : Wp →L[ℂ] Wp) :
    trY Y X = LinearMap.trace ℂ Wp (((ContinuousLinearMap.adjoint Y).comp X : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) :=
  rfl

lemma trY_self {Y : Wp →L[ℂ] Wp} (h : trY Y Y = 0) : Y = 0 := by
  set b := stdOrthonormalBasis ℂ Wp
  rw [trY_apply, LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, ⟪b i, (((ContinuousLinearMap.adjoint Y).comp Y : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) (b i)⟫_ℂ =
      ((‖Y (b i)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp only [h'] at h
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h
  have hb : ∀ i, Y (b i) = 0 := fun i => by
    have := h i (Finset.mem_univ _)
    simpa using this
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext (fun i => ?_)
  simp [hb i]

lemma trY_conj (Y X : Wp →L[ℂ] Wp) (e : Wp ≃ₗᵢ[ℂ] Wp)
    (h2 : Y.comp (e.symm : Wp →L[ℂ] Wp) = (e.symm : Wp →L[ℂ] Wp).comp Y) :
    trY Y ((e : Wp →L[ℂ] Wp).comp (X.comp (e.symm : Wp →L[ℂ] Wp))) = trY Y X := by
  have c : (e : Wp →L[ℂ] Wp).comp (ContinuousLinearMap.adjoint Y) =
      (ContinuousLinearMap.adjoint Y).comp (e : Wp →L[ℂ] Wp) := by
    have := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, e.symm.adjoint_eq_symm,
      LinearIsometryEquiv.symm_symm] at this
  have e1 : (ContinuousLinearMap.adjoint Y).comp ((e : Wp →L[ℂ] Wp).comp (X.comp (e.symm : Wp →L[ℂ] Wp))) =
      (e : Wp →L[ℂ] Wp).comp (((ContinuousLinearMap.adjoint Y).comp X).comp (e.symm : Wp →L[ℂ] Wp)) := by
    rw [← ContinuousLinearMap.comp_assoc, ← c]
    simp only [ContinuousLinearMap.comp_assoc]
  have e2 : ((((ContinuousLinearMap.adjoint Y).comp X).comp (e.symm : Wp →L[ℂ] Wp)).comp (e : Wp →L[ℂ] Wp)) =
      (ContinuousLinearMap.adjoint Y).comp X := by
    ext v
    simp
  have tc : ∀ A B : Wp →L[ℂ] Wp, LinearMap.trace ℂ Wp ((A.comp B : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) =
      LinearMap.trace ℂ Wp ((B.comp A : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) := fun A B =>
    LinearMap.trace_mul_comm (R := ℂ) (M := Wp) (A : Wp →ₗ[ℂ] Wp) (B : Wp →ₗ[ℂ] Wp)
  rw [trY_apply, trY_apply, e1, tc, e2]

end trace

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

lemma pi_eq (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    D.π h = ((piLIE D.z D.π D.π_rep D.π_unitary h hh : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma pi_inv_eq (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    D.π h⁻¹ = (((piLIE D.z D.π D.π_rep D.π_unitary h hh).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma adj_pi (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    ContinuousLinearMap.adjoint (D.π h) = D.π h⁻¹ := by
  rw [pi_eq D hh, LinearIsometryEquiv.adjoint_eq_symm, ← pi_inv_eq D hh]

lemma norm_pi_le (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) : ‖D.π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [D.π_unitary h hh v, one_mul]

lemma pi_inv_apply (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) (v : Wp) :
    D.π h⁻¹ (D.π h v) = v :=
  (piLIE D.z D.π D.π_rep D.π_unitary h hh).symm_apply_apply v

lemma pi_apply_inv (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) (v : Wp) :
    D.π h (D.π h⁻¹ v) = v :=
  (piLIE D.z D.π D.π_rep D.π_unitary h hh).apply_symm_apply v

lemma norm_ph (D : RealPlaceData k r Wp Wp) (p : SS k r) : ‖ph D p‖ = 1 := by
  have e : ∀ (z : Fin (2 * r + k + 1) → ℂ) (m : Mat k r), ‖psi k r z cStd m‖ = 1 := fun z m => by
    unfold psi
    rw [Complex.norm_exp]
    simp
  unfold ph
  rw [norm_mul, norm_star, e, e, one_mul]

lemma aesm_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → (Wp →L[ℂ] Wp)}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun a => (f a).comp (g a)) μ :=
  (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := Wp) (F := Wp) (G := Wp)).continuous.comp_aestronglyMeasurable
    (hf.prodMk hg)

lemma aesm_adj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → (Wp →L[ℂ] Wp)}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun a => ContinuousLinearMap.adjoint (f a)) μ :=
  (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).continuous.comp_aestronglyMeasurable hf

def Cf (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : Wp →L[ℂ] Wp :=
  (D.π (Matrix.of p.2.1)).comp ((ContinuousLinearMap.adjoint (D.π (Matrix.of p.1.1))).comp
    ((D.π (gbar k r γ (Matrix.of p.2.1))).comp (ContinuousLinearMap.adjoint (D.π (gbar k r γ (Matrix.of p.1.1))))))

def Cb (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : Wp →L[ℂ] Wp :=
  (D.π (gbar k r γ (Matrix.of p.1.1))).comp ((ContinuousLinearMap.adjoint (D.π (gbar k r γ (Matrix.of p.2.1)))).comp
    ((D.π (Matrix.of p.1.1)).comp (ContinuousLinearMap.adjoint (D.π (Matrix.of p.2.1)))))

lemma norm_C_le (D : RealPlaceData k r Wp Wp) {a b c d : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z)
    (hc : c ∈ UWset k r D.z) (hd : d ∈ UWset k r D.z) :
    ‖(D.π a).comp ((ContinuousLinearMap.adjoint (D.π b)).comp ((D.π c).comp (ContinuousLinearMap.adjoint (D.π d))))‖
      ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_one₀ (norm_pi_le D ha) (norm_nonneg _) ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  rw [LinearIsometryEquiv.norm_map]
  refine mul_le_one₀ (norm_pi_le D hb) (norm_nonneg _) ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_one₀ (norm_pi_le D hc) (norm_nonneg _) (norm_pi_le D hd)

lemma aesm_pi (D : RealPlaceData k r Wp Wp) (hclW : IsClosed (UWset k r D.z)) :
    AEStronglyMeasurable (fun x : Mt k r => D.π (Matrix.of x)) D.μW := by
  have hof : Continuous (⇑(Matrix.of : Mt k r ≃ Mat k r)) := by exact continuous_id
  have h : ContinuousOn (fun x : Mt k r => D.π (Matrix.of x)) (Matrix.of ⁻¹' UWset k r D.z) :=
    D.π_cont.comp hof.continuousOn (Set.mapsTo_preimage _ _)
  have h2 := h.aestronglyMeasurable (μ := D.μW) (hclW.preimage hof).measurableSet
  have hae : ∀ᵐ x ∂D.μW, x ∈ (Matrix.of ⁻¹' UWset k r D.z : Set (Mt k r)) :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2

variable (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
include hD hWbar

lemma psi_eq_C {p : SS k r} (hp : D.inSS p) (f : Mat k r → ℂ) (g : Mat k r) :
    Psi D γ f g p = (Phi D f g p).comp (Cf D γ p) ∧ Phi D f g p = (Psi D γ f g p).comp (Cb D γ p) ∧
      ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
  have hh := hp.1
  have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hD.z_eq ▸ hp.2.2.1
  have g1 := hWbar _ hh
  have g2 := hWbar _ hh'
  refine ⟨?_, ?_, norm_C_le D hh' hh g2 g1, norm_C_le D g1 g2 hh hh'⟩
  · ext v
    simp only [Phi, Psi, Cf, adj_pi D hh, adj_pi D g1, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_comp, _root_.smul_apply, pi_inv_apply D hh', pi_apply_inv D hh]
  · ext v
    simp only [Phi, Psi, Cb, adj_pi D hh', adj_pi D g2, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_comp, _root_.smul_apply, pi_inv_apply D g1, pi_apply_inv D g2]

omit hWbar in
lemma aesm_C (hclW : IsClosed (UWset k r D.z)) (hgW : D.μW.map (gb γ) = D.μW) :
    AEStronglyMeasurable (Cf D γ) D.μSS ∧ AEStronglyMeasurable (Cb D γ) D.μSS := by
  have := sfin D.haarW
  have := sfin D.haarN
  have hb := aesm_pi D hclW
  have hbg : AEStronglyMeasurable (fun x : Mt k r => D.π (gbar k r γ (Matrix.of x))) D.μW :=
    hb.comp_quasiMeasurePreserving (μ := D.μW) (f := gb γ)
      (MeasurePreserving.quasiMeasurePreserving ⟨(cont_gb γ).measurable, hgW⟩)
  have hSS : D.μSS = (D.μW.prod D.μN).prod (D.μW.prod D.μN) := by rw [RealPlaceData.μSS, hD.μW_eq]
  have q1 : Measure.QuasiMeasurePreserving (fun p : SS k r => p.1.1) D.μSS D.μW := by
    rw [hSS]; exact Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst
  have q2 : Measure.QuasiMeasurePreserving (fun p : SS k r => p.2.1) D.μSS D.μW := by
    rw [hSS]; exact Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
  have a1 := hb.comp_quasiMeasurePreserving q1
  have a2 := hb.comp_quasiMeasurePreserving q2
  have a3 := hbg.comp_quasiMeasurePreserving q1
  have a4 := hbg.comp_quasiMeasurePreserving q2
  exact ⟨aesm_comp a2 (aesm_comp (aesm_adj a1) (aesm_comp a4 (aesm_adj a3))),
    aesm_comp a3 (aesm_comp (aesm_adj a4) (aesm_comp a1 (aesm_adj a2)))⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymD
