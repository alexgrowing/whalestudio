import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntSOfSIntFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.JSIntFin
import Formalism.RealPlaceAnalysis.FinalF

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace CurveContinuity

open Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frob_eq_frobenius {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    frob g = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm g := by
  rw [@Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two]

theorem frob_mul_le {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : frob (a * b) ≤ frob a * frob b := by
  rw [frob_eq_frobenius, frob_eq_frobenius, frob_eq_frobenius]
  exact @Matrix.frobenius_norm_mul _ _ _ _ _ _ _ _ a b

theorem frob_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frob g := Real.sqrt_nonneg _

theorem frob_cont {n : ℕ} : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => frob g) := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((continuous_id.matrix_elem i j).norm).pow 2)

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = frob g := by
  unfold Formalism.FourierDecayAlt.B.gN frob
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem smooth_contOn {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) : ContinuousOn f (UJset ε) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFc : ContinuousAt F g := hF.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hFc.continuousWithinAt (s := UJset ε)).congr_of_eventuallyEq ?_ (hfF g hgU hg)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hgU)] with y hy hyU
  exact hfF y hyU hy

theorem exp_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t u : ℝ) :
    NormedSpace.exp ((u : ℂ) • X) =
      NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((u - t : ℝ) : ℂ) • X) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
  congr 2
  push_cast
  ring_nf

theorem hasDeriv_curve {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Formalism.REAL.Rd X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t))
  rw [Formalism.REAL.right_derivative_extends _ ε f F U g X hU hgU hg hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

theorem hasDeriv_curve_at {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X)))
      (Formalism.REAL.Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg' : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
    Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)
  have h0 := hasDeriv_curve hf hg' hX
  have h1 : HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((s : ℂ) • X)))
      (Formalism.REAL.Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  have h2 := h1.comp_sub_const t t
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  simp only
  rw [Matrix.mul_assoc, ← exp_shift X t u]

theorem curve_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X))
      (NormedSpace.exp ((t : ℂ) • X) * X) (t - t) := by
    rw [sub_self]; exact Formalism.REAL.hasDerivAt_mul_exp_smul_zero _ X
  refine ((h1.comp_sub_const t t).continuousAt).congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [← exp_shift X t u]

theorem rd_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (s : ℝ) : Formalism.REAL.Rd ((s : ℂ) • X) f g = (s : ℂ) * Formalism.REAL.Rd X f g := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • ((s : ℂ) • X)))) =
      (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) ∘ (fun t => s * t) := by
    funext t
    simp only [Function.comp, smul_smul]
    congr 3
    push_cast; ring_nf
  rw [h]
  have := deriv_comp_mul_left s (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
  simp only [mul_zero] at this
  rw [show ((fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) ∘ fun t => s * t) =
    (fun x => (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (s * x)) from rfl, this,
    Complex.real_smul]

theorem frob_pos {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ≠ 0) : 0 < frob g := by
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (Matrix.ext h)
  unfold frob
  apply Real.sqrt_pos.2
  calc (0 : ℝ) < ‖g i j‖ ^ 2 := pow_pos (norm_pos_iff.2 hij) 2
    _ ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

theorem ne_zero_of_inUJ {n : ℕ} (hn : 0 < n) {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : g ≠ 0 := by
  rintro rfl
  unfold Formalism.REAL.inUJ at hg
  have h := congrFun (congrFun hg ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.mul_zero, Matrix.zero_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at h
  split_ifs at h <;> norm_num at h

theorem one_mem_UH (k r : ℕ) : (1 : Mat k r) ∈ UH (Hpk k r) := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem uh_mul' {k r : ℕ} {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem inUJ_conj {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  obtain ⟨hPu, hPe⟩ := hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPe, ha']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1]; simp

theorem one_inUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold Formalism.REAL.inUJ; simp

section Int

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}

theorem ae_supp (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

def suppA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r}

theorem continuous_first_matrix : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst

theorem continuous_second_matrix : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd

theorem suppA_closed : IsClosed (suppA k r z) :=
  IsClosed.inter (IsClosed.preimage continuous_first_matrix (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).closed)
    (IsClosed.preimage continuous_second_matrix (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed)

theorem cont_gp (P x : Mat k r) :
    Continuous (fun p : Mt k r × Mt k r => P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
  (continuous_const.matrix_mul ((continuous_first_matrix.matrix_mul continuous_second_matrix).matrix_mul continuous_const)).matrix_mul
    continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  have hell : ∀ a, Continuous fun g : Mat k r => Formalism.MainNotions.S.ellA k r z g a := by
    intro a
    unfold Formalism.MainNotions.S.ellA
    split_ifs
    · exact continuous_id.matrix_elem _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

variable {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
  {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem chi_norm (hB : IsBData z c u π μW μN) {h : Mat k r} (hh : h ∈ UWset k r z) (m : Mat k r) (ξ : Vp) :
    ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π h m ξ‖ = ‖ξ‖ := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hU := hcTypeW_uRep k r z u Vp π hz hT hπ
  unfold chiInv Formalism.MainNotions.S.psiGen
  rw [norm_smul, norm_star, Complex.norm_exp_I_mul_ofReal, one_mul,
    hU.2.1 _ ((Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).inv_mem _ hh)]

theorem aesm_int {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp)
    (G : Mat k r → ℂ) (hG : ContinuousOn G (UJset ε)) (e : Mat k r) (he : Formalism.REAL.inUJ ε e) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * e) •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hU := hcTypeW_uRep k r z u Vp π hz hT hπ
  have hWc := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_supp hW hN)]
  refine ContinuousOn.aestronglyMeasurable ?_ suppA_closed.measurableSet
  refine ContinuousOn.smul ?_ ?_
  · refine hG.comp ((cont_gp P x).matrix_mul continuous_const).continuousOn ?_
    intro p hp
    exact Formalism.REAL.indefinite_unitary_mul_mem ε (inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)) he
  · unfold chiInv
    refine ContinuousOn.smul ((continuous_star.comp ((psiGen_cont z c).comp continuous_second_matrix)).continuousOn) ?_
    have hinv : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) (suppA k r z) := by
      intro p hp
      have hdet : IsUnit (Matrix.of p.1 : Mat k r).det := hWc.unit _ hp.1
      refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_matrix_inv _ ?_).comp continuous_first_matrix.continuousAt
      rw [← hdet.unit_spec]
      exact NormedRing.inverse_continuousAt hdet.unit
    exact (hU.2.2 ξ).comp hinv (fun p hp => hWc.inv_mem _ hp.1)

theorem bS_nonneg : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity

theorem int_bound {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (a : ℝ) (hb : S0.bS k r < a - 1) :
    Integrable (fun p : Mt k r × Mt k r => frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a))
      (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hIS := S0.IntS.intS_of_sIntFin (Mult1.S0.sIntFin Mult1.multiplicity_one_hypotheses_hold)
  have hI := hIS k r z μW μN hz hT hW hN 1 (one_mem_UH k r) x hx (a - 1) hb
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  set K := frob P⁻¹ * frob P with hKdef
  have hK : ∀ g : Mat k r, frob g ≤ K * frob (P * g * P⁻¹) := by
    intro g
    have hg : P⁻¹ * (P * g * P⁻¹) * P = g := by
      simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
    calc frob g = frob (P⁻¹ * (P * g * P⁻¹) * P) := by rw [hg]
      _ ≤ frob P⁻¹ * frob (P * g * P⁻¹) * frob P :=
          (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _))
      _ = K * frob (P * g * P⁻¹) := by rw [hKdef]; ring_nf
  have ha1 : 1 ≤ a := by linarith [bS_nonneg (k := k) (r := r)]
  refine Integrable.mono' (hI.const_mul (K ^ (a - 1))) ?_ ?_
  · exact ((frob_cont.comp (cont_gp P x)).measurable.pow_const _).aestronglyMeasurable
  · filter_upwards [ae_supp hW hN] with p hp
    have hgU : Matrix.of p.1 * Matrix.of p.2 * x ∈ UH (Hpk k r) := uh_mul' (uh_mul' hp.1.1 hp.2.1) hx
    have hJ := inUJ_conj hP hgU
    have hn : 0 < 2 * r + k + 1 := by omega
    have hG0 : 0 < frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) := frob_pos _ (ne_zero_of_inUJ hn hJ)
    have hg0 : 0 < frob (Matrix.of p.1 * Matrix.of p.2 * x) := by
      refine frob_pos _ ?_
      intro h
      apply ne_zero_of_inUJ hn hJ
      rw [h]; simp
    have hKg := hK (Matrix.of p.1 * Matrix.of p.2 * x)
    have hK0 : 0 < K := by
      by_contra hle
      push Not at hle
      have : K * frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle hG0.le
      linarith
    have hle : frob (Matrix.of p.1 * Matrix.of p.2 * x) / K ≤
        frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) := by
      rw [div_le_iff₀ hK0]; linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hG0.le _)]
    calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a)
        ≤ (frob (Matrix.of p.1 * Matrix.of p.2 * x) / K) ^ (1 - a) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hg0 hK0) hle (by linarith)
      _ = K ^ (a - 1) * Formalism.FourierDecayAlt.B.gN ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-(a - 1)) := by
          rw [inv_one, Matrix.one_mul, gN_eq_frob, Real.div_rpow hg0.le hK0.le, neg_sub, div_eq_mul_inv,
            ← Real.rpow_neg hK0.le, neg_sub, mul_comm]

end Int

end CurveContinuity

end ReciprocityTheory.ChartRestriction.DS.Lap
