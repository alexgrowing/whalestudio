import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem mc_sig_left (X : SigData k r) (u u' : X.Hs) {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) :
    mc X (X.σ b u) u' a = mc X u u' (a * b) := by
  unfold mc
  rw [X.rep.1.2 a ha b hb, ContinuousLinearMap.comp_apply]

private theorem Hpk_mul_self_eq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (if i.val < r ∨ r + k < i.val then i.rev else i)]
  · by_cases h : i.val < r ∨ r + k < i.val
    · rw [if_pos h]
      simp only [Hpk, Fin.val_rev, Fin.ext_iff, and_true]
      split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [if_neg h]
      simp only [Hpk, Fin.ext_iff, and_true]
      split_ifs <;> first | (exfalso; omega) | norm_num
  · intro l _ hl
    have hl' := l.isLt
    simp only [Hpk, Fin.ext_iff, Fin.val_rev, and_true, ne_eq] at hl ⊢
    split_ifs at hl ⊢ <;> (try simp only [ne_eq, Fin.ext_iff, Fin.val_rev] at hl) <;>
      first | (exfalso; omega) | norm_num
  · simp

private theorem mul_inv_and_inv_mul_of_mem_UH_Hpk {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Hpk_mul_self_eq_one]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hl
  exact ⟨Matrix.mul_nonsing_inv g hdet, Matrix.nonsing_inv_mul g hdet⟩

private theorem inv_mem_UH_Hpk {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  obtain ⟨h1, -⟩ := mul_inv_and_inv_mul_of_mem_UH_Hpk hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem mc_sig_right (X : SigData k r) (u u' : X.Hs) {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) :
    mc X u (X.σ b u') a = mc X u u' (b⁻¹ * a) := by
  obtain ⟨hinv, -⟩ := mul_inv_and_inv_mul_of_mem_UH_Hpk hb
  have hbi : b⁻¹ ∈ GV k r := inv_mem_UH_Hpk hb
  unfold mc
  have hcomp := X.rep.1.2 b hb b⁻¹ hbi
  rw [hinv, X.rep.1.1] at hcomp
  have hy : X.σ b (X.σ b⁻¹ (X.σ a u)) = X.σ a u := by
    have := congrArg (fun f : X.Hs →L[ℂ] X.Hs => f (X.σ a u)) hcomp
    simpa using this.symm
  let T : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ b : X.Hs →ₗ[ℂ] X.Hs), X.rep.2.1 b hb⟩
  rw [X.rep.1.2 b⁻¹ hbi a ha, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← hy]
  exact T.inner_map_map u' (X.σ b⁻¹ (X.σ a u))

theorem psiD_one (D : RealPlaceData k r Wp Wp) (hF : BEFacts D) (hN1 : (1 : Mat k r) ∈ Nset k r) :
    psiD D 1 = 1 := by
  have h := hF.pmul 1 hN1 1 hN1
  rw [mul_one] at h
  have hne : psiD D 1 ≠ 0 := by unfold psiD psi; exact Complex.exp_ne_zero _
  have h2 : psiD D 1 * (psiD D 1 - 1) = 0 := by rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.mp h0

theorem psiD_inv (D : RealPlaceData k r Wp Wp) (hF : BEFacts D) {m : Mat k r} (hm : m ∈ Nset k r) :
    psiD D m⁻¹ = star (psiD D m) := by
  have hmi : m⁻¹ ∈ Nset k r := hF.ninv m hm
  have h1 : m * m⁻¹ = 1 := (mul_inv_and_inv_mul_of_mem_UH_Hpk hm.1).1
  have hN1 : (1 : Mat k r) ∈ Nset k r := h1 ▸ hF.nmul m hm m⁻¹ hmi
  have hp := hF.pmul m hm m⁻¹ hmi
  rw [h1, psiD_one D hF hN1] at hp
  have hstar : psiD D m * star (psiD D m) = 1 := by
    unfold psiD psi
    simp only [Complex.star_def]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hne : psiD D m ≠ 0 := by unfold psiD psi; exact Complex.exp_ne_zero _
  exact mul_left_cancel₀ hne (hp.symm.trans hstar.symm)

def shG (m : Mat k r) (x y : Mt k r) : Mt k r := (Matrix.of y * (Matrix.of x * m * (Matrix.of x)⁻¹) : Mat k r)

def shL (h0 m : Mat k r) : Mt k r × Mt k r → Mt k r × Mt k r := fun p => (rmulF h0 p.1, shG m p.1 p.2)

def shR (h0 m : Mat k r) (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  ((h0⁻¹ * Matrix.of p.1 : Mat k r), (h0⁻¹ * (m⁻¹ * Matrix.of p.2) * h0⁻¹⁻¹ : Mat k r))

theorem measurable_shG (m : Mat k r) : Measurable (Function.uncurry (shG (k := k) (r := r) m)) := by
  have hG : Continuous fun p : Mt k r × Mt k r =>
      ((Matrix.of p.2 * (Matrix.of p.1 * m * (Matrix.of p.1 : Mat k r).adjugate) : Mat k r) : Mt k r) := by
    fun_prop
  have hs : Measurable fun p : Mt k r × Mt k r => ((Matrix.of p.1 : Mat k r).det)⁻¹ :=
    (Continuous.measurable (by fun_prop : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r).det)).inv
  have heq : Function.uncurry (shG (k := k) (r := r) m) = fun p =>
      fun i j => ((Matrix.of p.1 : Mat k r).det)⁻¹ *
        ((Matrix.of p.2 * (Matrix.of p.1 * m * (Matrix.of p.1 : Mat k r).adjugate) : Mat k r) : Mt k r) i j := by
    funext p i j
    simp only [Function.uncurry, shG, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply,
      smul_eq_mul]
  rw [heq]
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hs.mul ?_
  first
    | exact (hG.matrix_elem i j).measurable
    | exact (by fun_prop : Continuous fun p : Mt k r × Mt k r =>
        (Matrix.of p.2 * (Matrix.of p.1 * m * (Matrix.of p.1 : Mat k r).adjugate) : Mat k r) i j).measurable

theorem shL_mp (D : RealPlaceData k r Wp Wp) (hF : BEFacts D) {h0 m : Mat k r} (hh0 : h0 ∈ UWset k r D.z)
    (hm : m ∈ Nset k r) : MeasurePreserving (shL h0 m) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have hW : ∀ᵐ x ∂D.μW, (Matrix.of x : Mat k r) ∈ UWset k r D.z := ae_iff.mpr D.haarW.conc
  have hc : Continuous (rmulF (n := 2 * r + k + 1) h0) := by unfold rmulF; fun_prop
  have hf : MeasurePreserving (rmulF h0) D.μW D.μW := ⟨hc.measurable, D.haarW.right h0 hh0⟩
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : SigmaFinite D.μW := by
    first
      | infer_instance
      | exact sigmaFinite_of_locallyFinite
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  haveI : SigmaFinite D.μN := by
    first
      | infer_instance
      | exact sigmaFinite_of_locallyFinite
  unfold shL
  refine hf.skew_product (measurable_shG m) ?_
  filter_upwards [hW] with x hx
  obtain ⟨hc', -⟩ := hF.nrm _ hx m hm
  have e : shG m x = rmulF (Matrix.of x * m * (Matrix.of x)⁻¹) := rfl
  rw [e]
  exact D.haarN.right _ hc'

private theorem inv_mem_UWset' {z : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} (hg : g ∈ UWset k r z) :
    g⁻¹ ∈ UWset k r z := by
  obtain ⟨-, him⟩ := mul_inv_and_inv_mul_of_mem_UH_Hpk hg.1
  have fix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, him, Matrix.one_mulVec]
  exact ⟨inv_mem_UH_Hpk hg.1, fun a => ⟨fix _ (hg.2.1 a).1, fix _ (hg.2.1 a).2⟩, fix _ hg.2.2⟩

private theorem mul_mem_UH_Hpk {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem shR_mp (D : RealPlaceData k r Wp Wp) (hF : BEFacts D) {h0 m : Mat k r} (hh0 : h0 ∈ UWset k r D.z)
    (hm : m ∈ Nset k r) : MeasurePreserving (shR h0 m) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  haveI : SigmaFinite D.μW := by
    first
      | infer_instance
      | exact sigmaFinite_of_locallyFinite
  haveI : SigmaFinite D.μN := by
    first
      | infer_instance
      | exact sigmaFinite_of_locallyFinite
  have hlm : ∀ a : Mat k r, Continuous (lmulM (k := k) (r := r) a) := fun a => by unfold lmulM; fun_prop
  have hcm : ∀ a : Mat k r, Continuous (conjM (k := k) (r := r) a) := fun a => by unfold conjM; fun_prop
  have h1 : MeasurePreserving (lmulM h0⁻¹) D.μW D.μW :=
    ⟨(hlm _).measurable, D.haarW.left _ (inv_mem_UWset' hh0)⟩
  have h2 : MeasurePreserving (lmulM m⁻¹) D.μN D.μN := ⟨(hlm _).measurable, D.haarN.left _ (hF.ninv m hm)⟩
  have h3 : MeasurePreserving (conjM h0⁻¹) D.μN D.μN := ⟨(hcm _).measurable, hF.conj _ (inv_mem_UWset' hh0)⟩
  have e : shR h0 m = Prod.map (lmulM h0⁻¹) (conjM h0⁻¹ ∘ lmulM m⁻¹) := rfl
  rw [e]
  exact h1.prod (h3.comp h2)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem ae_mem_S (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r := by
  have h1 : ∀ᵐ x ∂D.μW, (Matrix.of x : Mat k r) ∈ UWset k r D.z := ae_iff.mpr D.haarW.conc
  have h2 : ∀ᵐ y ∂D.μN, (Matrix.of y : Mat k r) ∈ Nset k r := ae_iff.mpr D.haarN.conc
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem pi_cancel (D : RealPlaceData k r Wp Wp) {h0 : Mat k r} (hh0 : h0 ∈ UWset k r D.z) (w : Wp) :
    D.π h0 (D.π h0⁻¹ w) = w := by
  obtain ⟨hmi, him⟩ := mul_inv_and_inv_mul_of_mem_UH_Hpk hh0.1
  have fix : ∀ v, h0 *ᵥ v = v → h0⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, him, Matrix.one_mulVec]
  have hi : h0⁻¹ ∈ UWset k r D.z := by
    refine ⟨inv_mem_UH_Hpk hh0.1, fun a => ⟨fix _ (hh0.2.1 a).1, fix _ (hh0.2.1 a).2⟩, fix _ hh0.2.2⟩
  have h := D.π_rep.2 h0 hh0 h0⁻¹ hi
  rw [hmi, D.π_rep.1] at h
  have := congrArg (fun f : Wp →L[ℂ] Wp => f w) h
  simpa using this.symm

theorem beOp_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hF : BEFacts D) (u u' : X.Hs)
    (hI : Integrable (beInt D X u u') (D.μW.prod D.μN)) {h0 m : Mat k r} (hh0 : h0 ∈ UWset k r D.z)
    (hm : m ∈ Nset k r) :
    beOp D X (X.σ (m * h0) u) u' = psiD D m • (D.π h0).comp (beOp D X u u') := by
  set μ := D.μW.prod D.μN with hμ
  have hmp := shL_mp D hF hh0 hm
  have hIS : Integrable (fun p => beInt D X u u' (shL h0 m p)) μ :=
    (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI
  have hint : ∫ p, beInt D X u u' (shL h0 m p) ∂μ = ∫ p, beInt D X u u' p ∂μ := by
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hI.aestronglyMeasurable),
      hmp.map_eq]
  have hmi : m⁻¹ ∈ Nset k r := hF.ninv m hm
  have hm1 : m * m⁻¹ = 1 := (mul_inv_and_inv_mul_of_mem_UH_Hpk hm.1).1
  have hN1 : (1 : Mat k r) ∈ Nset k r := hm1 ▸ hF.nmul m hm m⁻¹ hmi
  have hpsi : psiD D m * star (psiD D m) = 1 := by
    rw [← psiD_inv D hF hm, ← hF.pmul m hm m⁻¹ hmi, hm1, psiD_one D hF hN1]
  have hπ : ∀ T : Wp →L[ℂ] Wp, (D.π h0).comp ((D.π h0⁻¹).comp T) = T := by
    intro T; ext w; simp only [ContinuousLinearMap.comp_apply]; exact pi_cancel D hh0 (T w)
  have hae : ∀ᵐ p ∂μ, beInt D X (X.σ (m * h0) u) u' p =
      psiD D m • (D.π h0).comp (beInt D X u u' (shL h0 m p)) := by
    filter_upwards [ae_mem_S D] with p hp
    obtain ⟨hh, hn⟩ := hp
    set h : Mat k r := Matrix.of p.1 with hdef
    set nn : Mat k r := Matrix.of p.2 with ndef
    have e1 : beInt D X u u' (shL h0 m p) = (mc X u u' (nn * (h * m * h⁻¹) * (h * h0)) *
        star (psiD D (nn * (h * m * h⁻¹)))) • D.π (h * h0)⁻¹ := rfl
    have e2 : beInt D X (X.σ (m * h0) u) u' p =
        (mc X (X.σ (m * h0) u) u' (nn * h) * star (psiD D nn)) • D.π h⁻¹ := rfl
    have hhi : h⁻¹ * h = 1 := (mul_inv_and_inv_mul_of_mem_UH_Hpk hh.1).2
    have e3 : nn * (h * m * h⁻¹) * (h * h0) = nn * h * (m * h0) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h⁻¹ h h0, hhi, Matrix.one_mul]
    obtain ⟨hc, hcp⟩ := hF.nrm h hh m hm
    have e4 : psiD D (nn * (h * m * h⁻¹)) = psiD D nn * psiD D m := by
      rw [hF.pmul nn hn _ hc, hcp]
    have e5 : D.π (h * h0)⁻¹ = (D.π h0⁻¹).comp (D.π h⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact D.π_rep.2 _ (inv_mem_UWset' hh0) _ (inv_mem_UWset' hh)
    have e6 := mc_sig_left X u u' (mul_mem_UH_Hpk hn.1 hh.1) (mul_mem_UH_Hpk hm.1 hh0.1)
    rw [e1, e2, e3, e4, e5, e6, ContinuousLinearMap.comp_smul, hπ, smul_smul, star_mul]
    congr 1
    linear_combination (-(mc X u u' (nn * h * (m * h0)) * star (psiD D nn))) * hpsi
  calc beOp D X (X.σ (m * h0) u) u' = ∫ p, beInt D X (X.σ (m * h0) u) u' p ∂μ := rfl
    _ = ∫ p, psiD D m • (D.π h0).comp (beInt D X u u' (shL h0 m p)) ∂μ := integral_congr_ae hae
    _ = psiD D m • ∫ p, (D.π h0).comp (beInt D X u u' (shL h0 m p)) ∂μ := integral_smul _ _
    _ = psiD D m • (D.π h0).comp (∫ p, beInt D X u u' (shL h0 m p) ∂μ) := by
        congr 1
        exact (ContinuousLinearMap.compL ℂ Wp Wp Wp (D.π h0)).integral_comp_comm hIS
    _ = psiD D m • (D.π h0).comp (beOp D X u u') := by rw [hint]; rfl

theorem beOp_right (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hF : BEFacts D) (u u' : X.Hs)
    (hI : Integrable (beInt D X u u') (D.μW.prod D.μN)) {h0 m : Mat k r} (hh0 : h0 ∈ UWset k r D.z)
    (hm : m ∈ Nset k r) :
    beOp D X u (X.σ (m * h0) u') = star (psiD D m) • (beOp D X u u').comp (D.π h0⁻¹) := by
  set μ := D.μW.prod D.μN with hμ
  have hmp := shR_mp D hF hh0 hm
  have hIS : Integrable (fun p => beInt D X u u' (shR h0 m p)) μ :=
    (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI
  have hint : ∫ p, beInt D X u u' (shR h0 m p) ∂μ = ∫ p, beInt D X u u' p ∂μ := by
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hI.aestronglyMeasurable),
      hmp.map_eq]
  have hmi : m⁻¹ ∈ Nset k r := hF.ninv m hm
  have hm1 : m * m⁻¹ = 1 := (mul_inv_and_inv_mul_of_mem_UH_Hpk hm.1).1
  have hN1 : (1 : Mat k r) ∈ Nset k r := hm1 ▸ hF.nmul m hm m⁻¹ hmi
  have hpsi : psiD D m * star (psiD D m) = 1 := by
    rw [← psiD_inv D hF hm, ← hF.pmul m hm m⁻¹ hmi, hm1, psiD_one D hF hN1]
  have hh0i : h0⁻¹ ∈ UWset k r D.z := inv_mem_UWset' hh0
  have hh0ii : h0⁻¹⁻¹ ∈ UWset k r D.z := inv_mem_UWset' hh0i
  have hinvinv : h0⁻¹⁻¹ * h0⁻¹ = 1 := (mul_inv_and_inv_mul_of_mem_UH_Hpk hh0i.1).2
  have hid : (D.π h0⁻¹⁻¹).comp (D.π h0⁻¹) = ContinuousLinearMap.id ℂ Wp := by
    have := D.π_rep.2 _ hh0ii _ hh0i
    rw [hinvinv, D.π_rep.1] at this
    exact this.symm
  have hae : ∀ᵐ p ∂μ, beInt D X u (X.σ (m * h0) u') p =
      star (psiD D m) • (beInt D X u u' (shR h0 m p)).comp (D.π h0⁻¹) := by
    filter_upwards [ae_mem_S D] with p hp
    obtain ⟨hh, hn⟩ := hp
    set h : Mat k r := Matrix.of p.1 with hdef
    set nn : Mat k r := Matrix.of p.2 with ndef
    have e1 : beInt D X u u' (shR h0 m p) =
        (mc X u u' (h0⁻¹ * (m⁻¹ * nn) * h0⁻¹⁻¹ * (h0⁻¹ * h)) *
          star (psiD D (h0⁻¹ * (m⁻¹ * nn) * h0⁻¹⁻¹))) • D.π (h0⁻¹ * h)⁻¹ := rfl
    have e2 : beInt D X u (X.σ (m * h0) u') p =
        (mc X u (X.σ (m * h0) u') (nn * h) * star (psiD D nn)) • D.π h⁻¹ := rfl
    have e6 := mc_sig_right X u u' (mul_mem_UH_Hpk hn.1 hh.1) (mul_mem_UH_Hpk hm.1 hh0.1)
    have e3 : h0⁻¹ * (m⁻¹ * nn) * h0⁻¹⁻¹ * (h0⁻¹ * h) = (m * h0)⁻¹ * (nn * h) := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h0⁻¹⁻¹ h0⁻¹ h, hinvinv, Matrix.one_mul]
    have e4 : psiD D (h0⁻¹ * (m⁻¹ * nn) * h0⁻¹⁻¹) = star (psiD D m) * psiD D nn := by
      obtain ⟨-, hcp⟩ := hF.nrm h0⁻¹ hh0i (m⁻¹ * nn) (hF.nmul _ hmi _ hn)
      rw [hcp, hF.pmul _ hmi _ hn, psiD_inv D hF hm]
    have e5 : D.π (h0⁻¹ * h)⁻¹ = (D.π h⁻¹).comp (D.π h0⁻¹⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact D.π_rep.2 _ (inv_mem_UWset' hh) _ hh0ii
    rw [e1, e2, e6, e3, e4, e5, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, hid,
      ContinuousLinearMap.comp_id, smul_smul, star_mul, star_star]
    congr 1
    linear_combination (-(mc X u u' ((m * h0)⁻¹ * (nn * h)) * star (psiD D nn))) * hpsi
  calc beOp D X u (X.σ (m * h0) u') = ∫ p, beInt D X u (X.σ (m * h0) u') p ∂μ := rfl
    _ = ∫ p, star (psiD D m) • (beInt D X u u' (shR h0 m p)).comp (D.π h0⁻¹) ∂μ := integral_congr_ae hae
    _ = star (psiD D m) • ∫ p, (beInt D X u u' (shR h0 m p)).comp (D.π h0⁻¹) ∂μ := integral_smul _ _
    _ = star (psiD D m) • (∫ p, beInt D X u u' (shR h0 m p) ∂μ).comp (D.π h0⁻¹) := by
        congr 1
        exact ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (D.π h0⁻¹)).integral_comp_comm hIS
    _ = star (psiD D m) • (beOp D X u u').comp (D.π h0⁻¹) := by rw [hint]; rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv
