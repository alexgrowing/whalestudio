import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.CutFold
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

variable {k r : ℕ}

def sP (p : Mt k r × Mt k r) : Mat k r := Matrix.of p.2 * Matrix.of p.1

def Fm (p : Mt k r × Mt k r) (x : Mt k r) : Mt k r := lmulM (sP p)⁻¹ x

def Gm (p : Mt k r × Mt k r) (x : Mt k r) : Mt k r := lmulM (sP p) x

private theorem continuous_sP : Continuous (fun p : Mt k r × Mt k r => (sP p : Mat k r)) := by
  have h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  exact h2.matrix_mul h1

private theorem measurable_inv_lemma_2 {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (A : X → Mat k r) (hA : Continuous A) :
    @Measurable X (Mt k r) _ _ (fun x => (((A x)⁻¹ : Mat k r) : Mt k r)) := by
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
  have e : (fun x => (((A x)⁻¹ : Mat k r) : Mt k r) i j) =
      fun x => ((A x).det)⁻¹ * (A x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [e]
  exact (hA.matrix_det.measurable.inv).mul ((hA.matrix_adjugate).matrix_elem i j).measurable

private theorem meas_of_cont_lemma_3 {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (F : X → Mat k r) (hF : Continuous F) :
    @Measurable X (Mt k r) _ _ (fun x => (F x : Mt k r)) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => (hF.matrix_elem i j).measurable

theorem measurable_sP : @Measurable (Mt k r × Mt k r) (Mt k r) _ _ (fun p => sP p) := by
  exact meas_of_cont_lemma_3 (k := k) (r := r) _ continuous_sP

theorem measurable_Fm : Measurable (Function.uncurry (Fm (k := k) (r := r))) := by
  have hi := measurable_inv_lemma_2 (fun q : (Mt k r × Mt k r) × Mt k r => (sP q.1 : Mat k r))
    (continuous_sP.comp continuous_fst)
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
  simp only [Function.uncurry, Fm, lmulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ (fun l _ => ?_)
  have h1 : Measurable (fun q : (Mt k r × Mt k r) × Mt k r => (((sP q.1)⁻¹ : Mat k r) : Mt k r) i l) :=
    measurable_pi_iff.mp (measurable_pi_iff.mp hi i) l
  have h2 : Measurable (fun q : (Mt k r × Mt k r) × Mt k r => q.2 l j) :=
    measurable_pi_iff.mp (measurable_pi_iff.mp measurable_snd l) j
  exact h1.mul h2

private theorem continuous_Gm_lemma : Continuous (fun q : (Mt k r × Mt k r) × Mt k r => (Gm q.1 q.2 : Mat k r)) := by
  have h1 : Continuous (fun q : (Mt k r × Mt k r) × Mt k r => (sP q.1 : Mat k r)) :=
    continuous_sP.comp continuous_fst
  have h2 : Continuous (fun q : (Mt k r × Mt k r) × Mt k r => (Matrix.of q.2 : Mat k r)) := continuous_snd
  exact h1.matrix_mul h2

theorem measurable_Gm : Measurable (Function.uncurry (Gm (k := k) (r := r))) := by
  exact meas_of_cont_lemma_3 (k := k) (r := r) _ continuous_Gm_lemma

theorem measurable_Gm_fst (x : Mt k r) : Measurable (fun p : Mt k r × Mt k r => Gm p x) := by
  exact meas_of_cont_lemma_3 (k := k) (r := r) (fun p : Mt k r × Mt k r => (Gm p x : Mat k r))
    (continuous_sP.matrix_mul (continuous_const : Continuous fun _ : Mt k r × Mt k r => (Matrix.of x : Mat k r)))

theorem pow_mul_le (hGL : GNLower) {g x : Mat k r} (hg : g ∈ GV k r) (hx : x ∈ GV k r) {A : ℝ} (hA : 0 ≤ A) :
    gN (g * x) ^ (-A) ≤ gN x⁻¹ ^ A * gN g ^ (-A) := by
  have hg1 : 1 ≤ gN g := hGL k r g hg
  have hsub : gN g ≤ gN (g * x) * gN x⁻¹ := by
    have e : g = (g * x) * x⁻¹ := by
      rw [Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv (k := k) (r := r) hx, Matrix.mul_one]
    calc gN g = gN ((g * x) * x⁻¹) := by rw [← e]
      _ ≤ gN (g * x) * gN x⁻¹ := ReciprocityTheory.ChartRestriction.DS.Mult1.bc_gN_mul_le _ _
  have hgpos : 0 < gN g := by linarith
  have hxi0 : 0 ≤ gN x⁻¹ := by unfold gN; exact Real.sqrt_nonneg _
  have hgx0 : 0 ≤ gN (g * x) := by unfold gN; exact Real.sqrt_nonneg _
  have hgxpos : 0 < gN (g * x) := by
    rcases hgx0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hsub; linarith
  have hA' : gN g ^ A ≤ gN (g * x) ^ A * gN x⁻¹ ^ A := by
    rw [← Real.mul_rpow hgx0 hxi0]
    exact Real.rpow_le_rpow hgpos.le hsub hA
  have ha : 0 < gN (g * x) ^ A := Real.rpow_pos_of_pos hgxpos A
  have hc : 0 < gN g ^ A := Real.rpow_pos_of_pos hgpos A
  rw [Real.rpow_neg hgxpos.le, Real.rpow_neg hgpos.le]
  calc (gN (g * x) ^ A)⁻¹ = (gN (g * x) ^ A)⁻¹ * gN g ^ A * (gN g ^ A)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hc.ne', mul_one]
    _ ≤ (gN (g * x) ^ A)⁻¹ * (gN (g * x) ^ A * gN x⁻¹ ^ A) * (gN g ^ A)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hc.le)
        exact mul_le_mul_of_nonneg_left hA' (inv_nonneg.2 ha.le)
    _ = gN x⁻¹ ^ A * (gN g ^ A)⁻¹ := by
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

def bet (x : Mt k r) : ℝ := gN (Matrix.of x : Mat k r) ^ (-AB k r)

private theorem continuous_gN_lemma : Continuous (fun x : Mt k r => gN (Matrix.of x : Mat k r)) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem measurable_bet : Measurable (bet (k := k) (r := r)) := by
  exact continuous_gN_lemma.measurable.pow_const _

theorem bet_nonneg (x : Mt k r) : 0 ≤ bet x := by
  unfold bet gN
  exact Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem AB_nonneg (k r : ℕ) : 0 ≤ AB k r := by
  unfold AB
  positivity

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def orbN (D : RealPlaceData k r Wp Wp) (x : Mt k r) : ℝ := ∫ p, bet (Gm p x) ∂(D.μW.prod D.μN)

theorem gnLower_of (h : UnitaryGroupStructuralFacts) : GNLower := by
  exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem measurable_bet_Gm (x : Mt k r) : Measurable (fun p : Mt k r × Mt k r => bet (Gm p x)) := by
  exact measurable_bet.comp (measurable_Gm_fst x)

theorem integrable_bet (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) {x : Mt k r}
    (hx : (Matrix.of x : Mat k r) ∈ GV k r) : Integrable (fun p => bet (Gm p x)) (D.μW.prod D.μN) := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have hGL : GNLower := gnLower_of h
  have hfin := ReciprocityTheory.ChartRestriction.DS.Mult1.bc_lintegral_S_pow_AB h D hD.μW_eq
  have hmeasB : Measurable (fun p : Mt k r × Mt k r =>
      ReciprocityTheory.ChartRestriction.DS.Mult1.bcPow (k := k) (r := r) (AB k r) (mulM (p.2, p.1))) :=
    (ReciprocityTheory.ChartRestriction.DS.Mult1.bc_measurable_pow (k := k) (r := r) (AB k r)).comp measurable_sP
  have hgi : Integrable (fun p : Mt k r × Mt k r =>
      (ReciprocityTheory.ChartRestriction.DS.Mult1.bcPow (k := k) (r := r) (AB k r) (mulM (p.2, p.1))).toReal)
      (D.μW.prod D.μN) :=
    integrable_toReal_of_lintegral_ne_top hmeasB.aemeasurable hfin.ne
  have hmul : ∀ u ∈ GV k r, ∀ v ∈ GV k r, u * v ∈ GV k r := by
    intro u hu v hv
    have hu' : uᴴ * Hpk k r * u = Hpk k r := hu
    have hv' : vᴴ * Hpk k r * v = Hpk k r := hv
    show (u * v)ᴴ * Hpk k r * (u * v) = Hpk k r
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at hu' hv' ⊢
    rw [← Matrix.mul_assoc (Hpk k r) u v, ← Matrix.mul_assoc uᴴ (Hpk k r * u) v, hu', hv']
  have hW0 : D.μW {y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z}ᶜ = 0 := D.haarW.conc
  have hN0 : D.μN {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r}ᶜ = 0 := D.haarN.conc
  have hae : ∀ᵐ p ∂(D.μW.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p.2 : Mat k r) ∈ Nset k r := by
    rw [ae_iff]
    refine measure_mono_null (t := ({y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z}ᶜ ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r}ᶜ)) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hW0, zero_mul]
      · rw [Measure.prod_prod, hN0, mul_zero]
  refine Integrable.mono' (hgi.const_mul (gN (Matrix.of x : Mat k r)⁻¹ ^ AB k r))
    (measurable_bet_Gm x).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hg : (Matrix.of (mulM (p.2, p.1)) : Mat k r) ∈ GV k r := hmul _ hp.2.1 _ hp.1.1
  have hle := pow_mul_le hGL hg hx (AB_nonneg k r)
  rw [Real.norm_of_nonneg (bet_nonneg _)]
  unfold ReciprocityTheory.ChartRestriction.DS.Mult1.bcPow
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _)]
  exact hle

theorem orbN_pos (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) {x : Mt k r}
    (hx : (Matrix.of x : Mat k r) ∈ GV k r) : 0 < orbN D x := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have hGL : GNLower := gnLower_of h
  have hint := integrable_bet h D hD hx
  have hmul : ∀ u ∈ GV k r, ∀ v ∈ GV k r, u * v ∈ GV k r := by
    intro u hu v hv
    have hu' : uᴴ * Hpk k r * u = Hpk k r := hu
    have hv' : vᴴ * Hpk k r * v = Hpk k r := hv
    show (u * v)ᴴ * Hpk k r * (u * v) = Hpk k r
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] at hu' hv' ⊢
    rw [← Matrix.mul_assoc (Hpk k r) u v, ← Matrix.mul_assoc uᴴ (Hpk k r * u) v, hu', hv']
  have hsub : {y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z} ×ˢ
      {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r} ⊆
      Function.support (fun p : Mt k r × Mt k r => bet (Gm p x)) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hg : (Matrix.of (Gm (a, b) x) : Mat k r) ∈ GV k r :=
      hmul _ (hmul _ hb.1 _ ha.1) _ hx
    have h1 := hGL k r _ hg
    rw [Function.mem_support]
    show gN (Matrix.of (Gm (a, b) x) : Mat k r) ^ (-AB k r) ≠ 0
    exact (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hA : D.μW {y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z} ≠ 0 := by
    intro h0
    have hc : D.μW {y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z}ᶜ = 0 := D.haarW.conc
    apply D.haarW.ne_zero
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ (zero_le')
    calc D.μW Set.univ = D.μW ({y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z} ∪
          {y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z}ᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
      _ = 0 := by rw [h0, hc, add_zero]
  have hB : D.μN {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r} ≠ 0 := by
    intro h0
    have hc : D.μN {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r}ᶜ = 0 := D.haarN.conc
    apply D.haarN.ne_zero
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ (zero_le')
    calc D.μN Set.univ = D.μN ({y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r} ∪
          {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r}ᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
      _ = 0 := by rw [h0, hc, add_zero]
  have hprod : (D.μW.prod D.μN) ({y : Mt k r | (Matrix.of y : Mat k r) ∈ UWset k r D.z} ×ˢ
      {y : Mt k r | (Matrix.of y : Mat k r) ∈ Nset k r}) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hA hB
  unfold orbN
  rw [integral_pos_iff_support_of_nonneg (fun p => bet_nonneg _) hint]
  exact lt_of_lt_of_le (pos_iff_ne_zero.2 hprod) (measure_mono hsub)

theorem orbN_inv (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {q : Mt k r × Mt k r}
    (hq : (Matrix.of q.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of q.2 : Mat k r) ∈ Nset k r) (x : Mt k r) :
    orbN D (Gm q x) = orbN D x := by
  have hT := shL_mp D (beFacts_of h D) hq.1 hq.2
  have hm : AEStronglyMeasurable (fun p => bet (Gm p x))
      ((D.μW.prod D.μN).map (shL (Matrix.of q.1) (Matrix.of q.2))) := (measurable_bet_Gm x).aestronglyMeasurable
  have e := integral_map hT.measurable.aemeasurable hm
  rw [hT.map_eq] at e
  unfold orbN
  rw [e]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_S D] with p hp
  have e1 : (Matrix.of (Gm p (Gm q x)) : Mat k r) =
      Matrix.of (Gm (shL (Matrix.of q.1) (Matrix.of q.2) p) x) := by
    show (Matrix.of p.2 * Matrix.of p.1 : Mat k r) * ((Matrix.of q.2 * Matrix.of q.1) * Matrix.of x) =
      (Matrix.of p.2 * (Matrix.of p.1 * Matrix.of q.2 * (Matrix.of p.1)⁻¹)) * (Matrix.of p.1 * Matrix.of q.1) * Matrix.of x
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.1 : Mat k r)⁻¹, gv_inv_mul hp.1.1, Matrix.one_mul]
  simp only [bet, e1]

theorem measurable_orbN (D : RealPlaceData k r Wp Wp) : Measurable (orbN D) := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have hc : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => (Gm q.2 q.1 : Mat k r)) := by
    have h1 : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => (sP q.2 : Mat k r)) :=
      continuous_sP.comp continuous_snd
    have h2 : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mat k r)) :=
      continuous_fst
    exact h1.matrix_mul h2
  have hm : Measurable (fun q : Mt k r × (Mt k r × Mt k r) => bet (Gm q.2 q.1)) :=
    measurable_bet.comp (meas_of_cont_lemma_3 (k := k) (r := r) _ hc)
  have hf : StronglyMeasurable
      (Function.uncurry fun (x : Mt k r) (p : Mt k r × Mt k r) => bet (Gm p x)) :=
    hm.stronglyMeasurable
  exact (hf.integral_prod_right (ν := D.μW.prod D.μN)).measurable

theorem foldS (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) :
    ∃ b : Mt k r → ℝ, Measurable b ∧ (∀ x, 0 ≤ b x) ∧
      ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (φ : Mt k r → E),
        Integrable φ D.μG →
        Integrable (fun p : (Mt k r × Mt k r) × Mt k r => b p.2 • φ (Fm p.1 p.2)) ((D.μW.prod D.μN).prod D.μG) ∧
          ∫ x, φ x ∂D.μG = ∫ x, b x • ∫ p, φ (Fm p x) ∂(D.μW.prod D.μN) ∂D.μG := by
  have sW := sigmaFinite_of_haarOn D.haarW
  have sN := sigmaFinite_of_haarOn D.haarN
  have sG := sigmaFinite_of_haarOn D.haarG
  have hb0 : ∀ x, 0 ≤ bet x / orbN D x := fun x =>
    div_nonneg (bet_nonneg x) (integral_nonneg fun p => bet_nonneg _)
  refine ⟨fun x => bet x / orbN D x, measurable_bet.div (measurable_orbN D), hb0, ?_⟩
  intro E _ _ _ φ hφ
  refine cutFold D.μG (D.μW.prod D.μN) Fm Gm measurable_Fm measurable_Gm ?_ ?_ (fun x => bet x / orbN D x)
    (measurable_bet.div (measurable_orbN D)) hb0 ?_ φ hφ
  · filter_upwards [ae_mem_S D] with p hp
    exact D.haarG.left _ (gv_inv (gv_mul hp.2.1 hp.1.1))
  · filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μG)).ae (ae_mem_S D)]
      with q hq
    have hs : sP q.1 ∈ GV k r := gv_mul hq.2.1 hq.1.1
    show (sP q.1 * ((sP q.1)⁻¹ * Matrix.of q.2) : Mat k r) = Matrix.of q.2
    rw [← Matrix.mul_assoc, gv_mul_inv hs, Matrix.one_mul]
  · filter_upwards [ae_mem_of_haarOn D.haarG] with x hx
    have hae : (fun p => bet (Gm p x) / orbN D x) =ᵐ[D.μW.prod D.μN] fun p => bet (Gm p x) / orbN D (Gm p x) := by
      filter_upwards [ae_mem_S D] with p hp
      rw [orbN_inv h D hp x]
    refine ⟨((integrable_bet h D hD hx).div_const _).congr hae, ?_⟩
    rw [← integral_congr_ae hae, integral_div]
    exact div_self (orbN_pos h D hD hx).ne'

end ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
