import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Transfer

noncomputable section

open Finset MeasureTheory Matrix Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgKeyTransfer

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.Lap.LemK PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma isOpen_omegaSet : IsOpen (OmegaSet n) := Ps1.isOpen_omega'

lemma omF_diffAt {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  PsW.diffAt hF.1 isOpen_omegaSet hz

lemma contDiffOn_vector_field_derivative (Y : Fin n → Fin n → ℂ) (F : (Fin n → Fin n → ℂ) → ℂ) (S : Set (Fin n → Fin n → ℂ))
    (hS : IsOpen S) (hF : ContDiffOn ℂ ⊤ F S) :
    ContDiffOn ℂ ⊤ (fun z => -(fderiv ℂ F z (PsW.mmul Y z))) S := by
  have h1 : ContDiffOn ℂ ⊤ (fderiv ℂ F) S := hF.fderiv_of_isOpen hS le_top
  have h2 : ContDiff ℂ ⊤ fun z : Fin n → Fin n → ℂ => PsW.mmul Y z :=
    PsW.contDiff_mmul contDiff_const contDiff_id
  exact (h1.clm_apply h2.contDiffOn).neg

lemma lop_mem (Y : Matrix (Fin n) (Fin n) ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    lop Y F ∈ OmF n := by
  refine ⟨?_, fun z hz => if_neg hz⟩
  exact (contDiffOn_vector_field_derivative Y F _ isOpen_omegaSet hF.1).congr fun z hz => if_pos hz

lemma phiO_mem (μ : Fin n → ℤ) : PhiO μ ∈ OmF n := by
  refine ⟨?_, fun z hz => Set.indicator_of_notMem hz _⟩
  exact (PsW.contDiffOn_phiQ μ).congr fun z hz => Set.indicator_of_mem hz _

lemma lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, if_pos hz, Pi.add_apply]
    have e := DFunLike.congr_fun
      ((omF_diffAt hF hz).hasFDerivAt.add (omF_diffAt hG hz).hasFDerivAt).fderiv (Y * z)
    exact (congrArg Neg.neg e).trans (neg_add _ _)
  · simp [lop, if_neg hz]

lemma lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    lop Y (c • F) = c • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, if_pos hz, Pi.smul_apply]
    have e := DFunLike.congr_fun ((omF_diffAt hF hz).hasFDerivAt.const_smul c).fderiv (Y * z)
    exact (congrArg Neg.neg e).trans (smul_neg c ((fderiv ℂ F z) (Y * z))).symm
  · simp [lop, if_neg hz]

lemma lop_zero (Y : Matrix (Fin n) (Fin n) ℂ) : lop Y (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) = 0 := by
  simpa using lop_smul Y 0 (OmF n).zero_mem

lemma lop_sum {ι : Type*} (Y : Matrix (Fin n) (Fin n) ℂ) (s : Finset ι) (c : ι → ℂ)
    (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : ∀ i, F i ∈ OmF n) :
    lop Y (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • lop Y (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lop_zero Y
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      lop_add Y ((OmF n).smul_mem _ (hF i)) ((OmF n).sum_mem fun j _ => (OmF n).smul_mem _ (hF j)),
      lop_smul Y _ (hF i), ih]

lemma lop_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Y : ι → Matrix (Fin n) (Fin n) ℂ)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    lop (∑ i ∈ s, c i • Y i) F = ∑ i ∈ s, c i • lop (Y i) F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, if_pos hz, Finset.sum_apply, Pi.smul_apply, Finset.sum_mul, map_sum,
      Matrix.smul_mul, map_smul, smul_neg, Finset.sum_neg_distrib]
  · simp [lop, if_neg hz]

def lwM (D : List (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  D.foldr lop F

lemma lw_mem (w : List (Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    lw w F ∈ OmF n := by
  induction w with
  | nil => exact hF
  | cons p w ih => exact lop_mem _ ih

lemma lWord_neg_eq {F F' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hFF : Set.EqOn F F' (OmegaSet n))
    (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    Set.EqOn (lWord (D.map Neg.neg) F) (lwM D F') (OmegaSet n) := by
  induction D with
  | nil => exact hFF
  | cons Z D ih =>
    intro z hz
    have hev : lWord (D.map Neg.neg) F =ᶠ[𝓝 z] lwM D F' :=
      Filter.eventually_of_mem (isOpen_omegaSet.mem_nhds hz) fun y hy => ih hy
    show fderiv ℂ (lWord (D.map Neg.neg) F) z (-Z * z) = lop Z (lwM D F') z
    rw [hev.fderiv_eq, lop, if_pos hz, Matrix.neg_mul, map_neg]

lemma lwM_expand {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    ∀ (l : ℕ) (c : Fin l → Fin n × Fin n → ℂ),
      lwM (List.ofFn fun i => ∑ q : Fin n × Fin n, c i q • Matrix.single q.1 q.2 (1 : ℂ)) F =
        ∑ w' : Fin l → Fin n × Fin n, (∏ i, c i (w' i)) • lw (List.ofFn w') F
  | 0, c => by simp [lwM, lw]
  | l + 1, c => by
    rw [List.ofFn_succ]
    show lop _ (lwM _ F) = _
    rw [lwM_expand hF l (fun i => c i.succ), lop_sum_left,
      ← (Fin.consEquiv (fun _ : Fin (l + 1) => Fin n × Fin n)).sum_comp
        (fun w' => (∏ i, c i (w' i)) • lw (List.ofFn w') F)]
    conv_rhs => rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro q _
    rw [lop_sum _ _ _ _ fun w' => lw_mem _ hF, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w' _
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, smul_smul]
    rfl

lemma conj_single {ε : Fin n → Bool} (k : KG ε) (p : Fin n × Fin n) :
    toMK k⁻¹ * Matrix.single p.1 p.2 (1 : ℂ) * toMK k =
      ∑ q : Fin n × Fin n, adC (toMK k⁻¹) p q • Matrix.single q.1 q.2 (1 : ℂ) := by
  have hinv : (toMK k⁻¹)⁻¹ = toMK k := Matrix.inv_eq_left_inv (PsW.toMK_mul_inv k)
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.mul_assoc, Matrix.mul_apply]
  simp [adC, hinv, Matrix.mul_apply, Matrix.single_apply, Matrix.smul_apply, ite_and]

lemma lWord_adW_expand {ε : Fin n → Bool} (μ : Fin n → ℤ) (k : KG ε) {l : ℕ} (w : Fin l → Fin n × Fin n)
    {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    lWord (adW ε k (((List.ofFn w).map fun p => Matrix.single p.1 p.2 (1 : ℂ)).map Neg.neg)) (PhiM μ) y =
      ∑ w' : Fin l → Fin n × Fin n, (∏ i, adC (toMK k⁻¹) (w i) (w' i)) * lw (List.ofFn w') (PhiO μ) y := by
  have hD : adW ε k ((List.ofFn w).map fun p => Matrix.single p.1 p.2 (1 : ℂ)) =
      List.ofFn fun i => ∑ q : Fin n × Fin n, adC (toMK k⁻¹) (w i) q • Matrix.single q.1 q.2 (1 : ℂ) := by
    simp only [adW, List.map_ofFn]
    congr 1
    funext i
    exact conj_single k (w i)
  rw [tt_adW_neg, hD, lWord_neg_eq (F' := PhiO μ) (fun z hz => (Set.indicator_of_mem hz _).symm) _ hy,
    lwM_expand (phiO_mem μ) l fun i q => adC (toMK k⁻¹) (w i) q]
  simp [Finset.sum_apply]

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma sum_swap {ι : Type*} [Fintype ι] (A : ι → ι → ℂ) (B C : ι → ℂ) :
    ∑ w', (∑ w, A w w' * B w) * C w' = ∑ w, B w * ∑ w', A w w' * C w' := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  ring

lemma betaF_rhoA (T : KType ε Λ) (μ : Fin n → ℤ) (m : ℕ) (κ : KG ε) (a : AS T m)
    (y : Matrix (Fin n) (Fin n) ℂ) :
    betaF T μ (rhoA T m κ a) y = ∑ x : Wd n m, inner ℂ T.w (T.op κ (a x)) *
      ∑ w' : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK κ) (x.2 i) (w' i)) * lw (List.ofFn w') (PhiO μ) y := by
  have hrho : ∀ (l : Fin (m + 1)) (w' : Fin l → Fin n × Fin n), inner ℂ T.w (rhoA T m κ a ⟨l, w'⟩) =
      ∑ w : Fin l → Fin n × Fin n, (∏ i, adC (toMK κ) (w i) (w' i)) * inner ℂ T.w (T.op κ (a ⟨l, w⟩)) := by
    intro l w'
    simp only [rhoA, inner_sum, inner_smul_right]
  simp only [betaF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ofW]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hrho]
  exact sum_swap (ι := Fin l → Fin n × Fin n) (fun w w' => ∏ i, adC (toMK κ) (w i) (w' i))
    (fun w => inner ℂ T.w (T.op κ (a ⟨l, w⟩))) fun w' => lw (List.ofFn w') (PhiO μ) y

lemma lWord_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (ℓ : E →L[ℂ] E') {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {P : Matrix (Fin n) (Fin n) ℂ → E} (hP : ∀ D, DifferentiableOn ℂ (lWord D P) U)
    (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    Set.EqOn (lWord D fun y => ℓ (P y)) (fun y => ℓ (lWord D P y)) U := by
  induction D with
  | nil => exact fun _ _ => rfl
  | cons Z D ih =>
    intro z hz
    have hev : lWord D (fun y => ℓ (P y)) =ᶠ[𝓝 z] fun y => ℓ (lWord D P y) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => ih hy
    have hd := ((hP D).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have h := (ℓ.hasFDerivAt.comp z hd).fderiv
    show fderiv ℂ (lWord D fun y => ℓ (P y)) z (Z * z) = ℓ (fderiv ℂ (lWord D P) z (Z * z))
    rw [hev.fderiv_eq]
    exact DFunLike.congr_fun h _

lemma eword_local (ε : Fin n → Bool) {F f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (hdiff : ∀ D, DifferentiableOn ℂ (lWord D F) U) (hWU : ∀ g ∈ W, g⁻¹ * m ∈ U)
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) (L : List (Fin n × Fin n)) :
    ∀ g ∈ W, inUJ ε g → Formalism.REAL.Eword ε L f g =
      lWord ((L.map fun p => Matrix.single p.1 p.2 (1 : ℂ)).map Neg.neg) F (g⁻¹ * m) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    intro g hg hgu
    exact ta_ecV_local ε hW hg hgu ((hdiff _).differentiableAt (hU.mem_nhds (hWU g hg))) ih
      (Matrix.single p.1 p.2 (1 : ℂ))

lemma continuous_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k :=
  continuous_subtype_val.comp T.cont

lemma word_formula [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {k₀ : KG ε} (hU : IsOpen U) (hW : IsOpen W)
    (hword : ∀ D : List (Matrix (Fin n) (Fin n) ℂ),
        DifferentiableOn ℂ (lWord D (psM T μ)) U ∧
        (∀ z ∈ U, Continuous fun k : KG ε => lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k)) ∧
        ∀ z ∈ U, lWord D (psM T μ) z =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
    (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ U)
    (hloc : ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀))
    (v : T.V) (L : List (Fin n × Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    Formalism.REAL.Eword ε L (fun h => inner ℂ T.w (PsiM T μ h v)) g =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) *
        ∫ k, lWord (adW ε k ((L.map fun p => Matrix.single p.1 p.2 (1 : ℂ)).map Neg.neg)) (PhiM μ)
            (toMK k⁻¹ * (g⁻¹ * toMK k₀) * toMK k) *
          (inner ℂ T.w (T.op k⁻¹ v) * inner ℂ T.w (T.op (k₀ * k) T.w)) ∂(muK ε) := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  let ℓ : (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    (innerSL ℂ T.w).comp ((T.op k₀).comp (ContinuousLinearMap.apply ℂ T.V v))
  have hEq := fun D => lWord_clm ℓ hU (fun D => (hword D).1) D
  have hdiff : ∀ D, DifferentiableOn ℂ (lWord D fun y => ℓ (psM T μ y)) U := fun D =>
    (ℓ.differentiable.comp_differentiableOn (hword D).1).congr (hEq D)
  have hz : g⁻¹ * toMK k₀ ∈ U := (hWU g hg).2
  have hf : ∀ h ∈ W, inUJ ε h → inner ℂ T.w (PsiM T μ h v) = ℓ (psM T μ (h⁻¹ * toMK k₀)) :=
    fun h hh hhu => by rw [hloc h hh hhu]; rfl
  set D := (L.map fun p => Matrix.single p.1 p.2 (1 : ℂ)).map Neg.neg with hDdef
  have hA : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := Ps1.continuous_P T
  have hint : Integrable (fun k : KG ε => lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * (g⁻¹ * toMK k₀) * toMK k) •
      (T.op k * projW T * T.op k⁻¹)) (muK ε) :=
    integrableOn_univ.mp ((((hword D).2.1 _ hz).smul hA).continuousOn.integrableOn_compact isCompact_univ)
  rw [eword_local ε hU hW hdiff (fun h hh => (hWU h hh).2) hf L g hg hgu, hEq D hz]
  show ℓ (lWord D (psM T μ) (g⁻¹ * toMK k₀)) = _
  rw [(hword D).2.2 _ hz, map_smul, smul_eq_mul, ← ContinuousLinearMap.integral_comp_comm ℓ hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show ℓ (_ • _) = _
  rw [map_smul, smul_eq_mul]
  congr 1
  show inner ℂ T.w (T.op k₀ ((T.op k * projW T * T.op k⁻¹) v)) = _
  have hAv : (T.op k * projW T * T.op k⁻¹) v = inner ℂ T.w (T.op k⁻¹ v) • T.op k T.w := by
    simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, map_smul]
  rw [hAv, map_smul, inner_smul_right, op_mul']
  rfl

theorem transfer : Transfer := by
  intro n ε lam T μ m _hlam hμ a g₀ hg₀
  obtain ⟨U, hU, hpos, hconj, hword⟩ := psM_word n ε (lowK ε lam) T μ
  obtain ⟨W, k₀, hW, hg₀W, hWU, hloc⟩ := psiM_local T μ hμ U hU hpos hg₀
  refine ⟨W, hW.mem_nhds hg₀W, k₀, fun g hgW hgU => ?_⟩
  have := compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have hz : g⁻¹ * toMK k₀ ∈ U := (hWU g hgW).2
  have hop := continuous_op T
  have hint : ∀ x ∈ (univ : Finset (Wd n m)), Integrable (fun k : KG ε =>
      lWord (adW ε k (((ofW x).map fun p => Matrix.single p.1 p.2 (1 : ℂ)).map Neg.neg)) (PhiM μ)
          (toMK k⁻¹ * (g⁻¹ * toMK k₀) * toMK k) *
        (inner ℂ T.w (T.op k⁻¹ (a x)) * inner ℂ T.w (T.op (k₀ * k) T.w))) (muK ε) := fun x _ => by
    have h1 : Continuous fun k : KG ε => inner ℂ T.w (T.op k⁻¹ (a x)) :=
      continuous_const.inner ((hop.comp continuous_inv).clm_apply continuous_const)
    have h2 : Continuous fun k : KG ε => inner ℂ T.w (T.op (k₀ * k) T.w) :=
      continuous_const.inner ((hop.comp (continuous_const.mul continuous_id)).clm_apply continuous_const)
    exact integrableOn_univ.mp
      ((((hword _).2.1 _ hz).mul (h1.mul h2)).continuousOn.integrableOn_compact isCompact_univ)
  unfold actF
  rw [Finset.sum_apply, Finset.sum_congr rfl fun x _ =>
    word_formula T μ hU hW hword hWU hloc (a x) (ofW x) hgW hgU, ← Finset.mul_sum,
    ← integral_finsetSum _ hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show ∑ x : Wd n m, _ = betaF T μ (rhoA T m k⁻¹ a) (toMK k⁻¹ * (g⁻¹ * toMK k₀) * toMK k) * inner ℂ T.w (T.op (k₀ * k) T.w)
  rw [betaF_rhoA, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show ofW x = List.ofFn x.2 from rfl, lWord_adW_expand μ k x.2 (hconj _ hz k)]
  ring

end GlobalTheory.CompanionTheory.RgKeyTransfer
