import Formalism.LocalToGlobal.InertKernelTheory.KerTransAll
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4 kernel4 alphaQ stdH matH)

def PeriodPairTranscendence (L : PeriodPair) (ω₀ : ℂ) : Prop :=
  ∀ s : ℂ, (∃ N : ℕ, 0 < N ∧ (N : ℂ) * s ∈ L.lattice) →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      CoefIn1 (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) M

def PeriodTranscendenceAllLattices : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → PeriodPairTranscendence B.L B.ω₀

namespace AlgP

section OneVar

variable {W : Type} [Fintype W] [DecidableEq W]

theorem translation_operator_analytic (L : PeriodPair) (s : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ (Formalism.L2.Th1.F.opU L s f) Set.univ := by
  have hd : Differentiable ℂ (Formalism.L2.Th1.F.opU L s f) := by
    have h1 : Differentiable ℂ (fun z : ℂ => f (z + s)) := hf.comp (differentiable_id.add_const s)
    have h2 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z s
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L s s / 2)) := by
      unfold Formalism.L2.Th1.F.herm
      fun_prop
    exact h1.mul h2
  exact fun z _ => hd.analyticAt z

theorem coefInMv_prodFn (M : IntermediateField ℚ ℂ) (f : W → ℂ → ℂ) (hf : ∀ w, AnalyticAt ℂ (f w) 0)
    (hM : ∀ w, CoefIn1 (f w) M) : CoefInMv (Formalism.L2.Th1.H.prodFn f) M := by
  intro ν
  rw [Formalism.L2.Th1.H.taylorMvProd W f hf]
  suffices h : ∀ s : Finset W, ∀ ν : W →₀ ℕ,
      MvPowerSeries.coeff ν (∏ w ∈ s, Formalism.InvariantFactorPaths.G7.at1 w (Formalism.L2.Th1.F.taylor0 (f w))) ∈ M from h _ ν
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro ν
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert a s ha ih =>
    intro ν
    rw [Finset.prod_insert ha, MvPowerSeries.coeff_mul]
    refine sum_mem fun p _ => mul_mem ?_ (ih p.2)
    rw [Formalism.InvariantFactorPaths.G7.coeff_single_variable_series]
    split_ifs
    · exact hM a _
    · exact zero_mem _

theorem prodFn_analytic (f : W → ℂ → ℂ) (hf : ∀ w, Differentiable ℂ (f w)) :
    AnalyticOnNhd ℂ (Formalism.L2.Th1.H.prodFn f) Set.univ := by
  have h := coefInMv_prod (fun (b : W) (z : W → ℂ) => f b (z b))
    (fun b z _ => AnalyticAt.comp (g := f b) (f := fun y : W → ℂ => y b) ((hf b).analyticAt (z b))
      ((ContinuousLinearMap.proj b : (W → ℂ) →L[ℂ] ℂ).analyticAt z)) ⊤
    (fun b ν => IntermediateField.mem_top)
  exact h.2

theorem coefInMv_sum {ι : Type} [Fintype ι] [DecidableEq ι] {β : Type} (S : Finset β) (c : β → ℂ)
    (F : β → (ι → ℂ) → ℂ) (hF : ∀ b, AnalyticOnNhd ℂ (F b) Set.univ) (M : IntermediateField ℚ ℂ)
    (hc : ∀ b ∈ S, c b ∈ M) (hM : ∀ b ∈ S, CoefInMv (F b) M) :
    CoefInMv (fun z => ∑ b ∈ S, c b * F b z) M ∧ AnalyticOnNhd ℂ (fun z => ∑ b ∈ S, c b * F b z) Set.univ := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨coefInMv_const M 0 (zero_mem _), analyticOnNhd_const⟩
  | insert a s ha ih =>
    have ih' := ih (fun b hb => hc b (Finset.mem_insert_of_mem hb)) (fun b hb => hM b (Finset.mem_insert_of_mem hb))
    have e : (fun z => ∑ b ∈ insert a s, c b * F b z) = fun z => c a * F a z + ∑ b ∈ s, c b * F b z := by
      funext z
      rw [Finset.sum_insert ha]
    rw [e]
    have hA : AnalyticOnNhd ℂ (fun z => c a * F a z) Set.univ := fun z hz => analyticAt_const.mul (hF a z hz)
    refine ⟨?_, fun z hz => (hA z hz).add (ih'.2 z hz)⟩
    intro ν
    rw [(Formalism.L2.Th1.H.taylorMvLinear ι (fun z => c a * F a z) (fun z => ∑ b ∈ s, c b * F b z)
      (hA 0 (Set.mem_univ _)) (ih'.2 0 (Set.mem_univ _))).1, map_add]
    refine add_mem ?_ (ih'.1 ν)
    rw [(Formalism.L2.Th1.H.taylorMvLinear ι (F a) (F a) (hF a 0 (Set.mem_univ _)) (hF a 0 (Set.mem_univ _))).2 (c a),
      MvPowerSeries.coeff_C_mul]
    exact mul_mem (hc a (Finset.mem_insert_self a s)) (hM a (Finset.mem_insert_self a s) ν)

theorem coefInMv_comp_lin {ι : Type} [Fintype ι] [DecidableEq ι] (G : (ι → ℂ) → ℂ) (hG : AnalyticAt ℂ G 0)
    (g : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (M : IntermediateField ℚ ℂ) (hg : ∀ i j, LinearMap.toMatrix' g i j ∈ M)
    (h : CoefInMv G M) : CoefInMv (fun z => G (g z)) M := by
  have e : (fun z => G (g z)) = fun z => G ((LinearMap.toMatrix' g).mulVec z) := by
    funext z
    rw [LinearMap.toMatrix'_mulVec]
  intro ν
  rw [e, Formalism.L2.Th1.H.taylorMvComp ι ι _ G hG]
  exact coefIn_linSubst M _ hg _ h ν

theorem mat_inv_mem (K : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m] (A Bm : Matrix m m ℂ)
    (hAB : A * Bm = 1) (hA : ∀ i j, A i j ∈ K) : ∀ i j, Bm i j ∈ K := by
  let φ : K →+* ℂ := algebraMap K ℂ
  let AK : Matrix m m K := fun i j => ⟨A i j, hA i j⟩
  have hmap : AK.map φ = A := by
    ext i j
    rfl
  have hdA : A.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdet : IsUnit AK.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdA ?_
    rw [← hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have h2 : A * (AK⁻¹).map φ = 1 := by
    rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have h3 : Bm * A = 1 := mul_eq_one_comm.mp hAB
  have hB : Bm = (AK⁻¹).map φ := by
    calc Bm = Bm * (A * (AK⁻¹).map φ) := by rw [h2, Matrix.mul_one]
      _ = (AK⁻¹).map φ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  intro i j
  rw [hB]
  exact (AK⁻¹ i j).2

theorem exists_nf (T : Finset ℂ) (h : ∀ x ∈ T, x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ x ∈ T, x ∈ M := by
  refine ⟨IntermediateField.adjoin ℚ (T : Set ℂ), ?_, fun x hx => IntermediateField.subset_adjoin ℚ _ hx⟩
  exact IntermediateField.finiteDimensional_adjoin fun x hx => (mem_algebraicClosure_iff.1 (h x hx)).isIntegral

theorem rootOfUnity_mem_Qbar {z : ℂ} {k : ℕ} (hk : 0 < k) (h : z ^ k = 1) : z ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hk ?_)
  rw [h]
  exact isAlgebraic_one

theorem sqrtNat_mem_Qbar (n : ℕ) : ((Real.sqrt n : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2) two_pos ?_)
  have e : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    push_cast
    rfl
  rw [e]
  exact isAlgebraic_natCast n

end OneVar

section Main

open Formalism.L2.Th1.H (imgLat pow4 stdLat relIdx altE IsReps dualLat)

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem embT_mem_Qbar (τ : D.what₂.Tau) (x : D.host.E) : Formalism.MainNotions.TaylorLogMetric.embT D τ x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (Formalism.MainNotions.TaylorLogMetric.embT D τ).toRatAlgHom).isAlgebraic

theorem gC_symm_single (B : Ker.Base D cc δ) (w : Fin 4 × D.what₂.Tau) :
    B.gC.symm (Pi.single w 1) = fun w' => Formalism.MainNotions.TaylorLogMetric.embT D w'.2 (B.γ₀.g.symm (Pi.single w 1) w'.1) := by
  rw [LinearEquiv.symm_apply_eq, B.gC_spec, LinearEquiv.apply_symm_apply]
  funext w'
  by_cases hw : w' = w
  · subst hw
    simp
  · simp [hw]

theorem gC_mat_mem (B : Ker.Base D cc δ) (i j : Fin 4 × D.what₂.Tau) :
    LinearMap.toMatrix' (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) i j ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have hA : ∀ i j, LinearMap.toMatrix' (B.gC.symm : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) i j
      ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro i j
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, gC_symm_single]
    exact embT_mem_Qbar _ _
  refine mat_inv_mem _ _ _ ?_ hA i j
  rw [← LinearMap.toMatrix'_comp]
  have h : ((B.gC.symm : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)).comp
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))) = LinearMap.id := by
    ext x
    simp
  rw [h, LinearMap.toMatrix'_id]

theorem kerTransAlg_of (B : Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h1 : PeriodPairTranscendence B.L B.ω₀) : KerTransAlg B := by
  intro t ht
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have sd := hS
  obtain ⟨S, hSr⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ sd.idx₁).1
  have hshape := Formalism.L2.Th1.H.quadraticSemicharacter_identity_reformulated₂ B.L B.ω₀ D.what₂.Tau (Ker.hOne B.L D.what₂.Tau) B.lamM _ _ B.gC hS
    B.kappa B.thMM (fourth_tensor_theta_eq_kernel B hS) S hSr t
  set v : Fin 4 × D.what₂.Tau → ℂ := B.gC (fun w => t w.2) with hv_def
  set th := Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) with hth
  set r : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun x => B.kappa * ((Real.sqrt (relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))) : ℝ) : ℂ)⁻¹
      * alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)) with hr
  set f : (Fin 4 × D.what₂.Tau → ℂ) → Fin 4 × D.what₂.Tau → ℂ → ℂ :=
    fun x w => Formalism.L2.Th1.F.opU B.L (v w + x w) th with hf
  set G : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun y => ∑ x ∈ S, r x * Formalism.L2.Th1.H.prodFn (f x) y with hG
  have hthd : Differentiable ℂ th := (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ sd.per sd.half).1

  have hT : Formalism.L2.Th1.H.opU (stdH B.L (Fin 4 × D.what₂.Tau)) (diag4 t) (kerB B) = fun z => B.kappa⁻¹ * G (B.gC z) := by
    have h4 : tens4 (Formalism.L2.Th1.H.opU (matH (Ker.hOne B.L D.what₂.Tau)) t B.thMM)
        = B.kappa • Formalism.L2.Th1.H.opU (stdH B.L (Fin 4 × D.what₂.Tau)) (diag4 t) (kerB B) := by
      rw [fourth_tensor_translate, fourth_tensor_theta_eq_kernel B hS, opU_smul]
      rfl
    funext z
    have hz := hshape (B.gC z)
    rw [LinearEquiv.symm_apply_apply, h4] at hz
    rw [show G (B.gC z) = B.kappa * Formalism.L2.Th1.H.opU (stdH B.L (Fin 4 × D.what₂.Tau)) (diag4 t) (kerB B) z from hz.symm,
      ← mul_assoc, inv_mul_cancel₀ B.kappa_ne_zero, one_mul]

  obtain ⟨m, hm, hmt⟩ := ht
  have hmv : (m : ℂ) • v ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    refine AddSubgroup.mem_map.2 ⟨(m : ℂ) • (fun w : Fin 4 × D.what₂.Tau => t w.2), fun a => hmt, ?_⟩
    show B.gC ((m : ℂ) • fun w : Fin 4 × D.what₂.Tau => t w.2) = (m : ℂ) • v
    rw [map_smul]
  obtain ⟨N1, hN1, hup⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.up B
  have htor : ∀ x ∈ S, ∀ w, ∃ N : ℕ, 0 < N ∧ (N : ℂ) * (v w + x w) ∈ B.L.lattice := by
    intro x hx w
    have ha := ((AddSubgroup.mem_pi Set.univ).1 (hup _ hmv)) w (Set.mem_univ _)
    have hb := ((AddSubgroup.mem_pi Set.univ).1 (hup _ (hSr.1 x hx))) w (Set.mem_univ _)
    refine ⟨N1 * m, Nat.mul_pos hN1 hm, ?_⟩
    have e : ((N1 * m : ℕ) : ℂ) * (v w + x w) = (N1 • ((m : ℂ) • v)) w + m • ((N1 • x) w) := by
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact add_mem ha (nsmul_mem hb m)

  have hrQ : ∀ x ∈ S, r x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro x hx
    have hx2 := hSr.1 x hx
    refine mul_mem (mul_mem (mul_mem (mem_algebraicClosure_iff.2 (kapAlg_all B)) (inv_mem (sqrtNat_mem_Qbar _))) ?_) ?_
    · rcases sd.betaSemi.1 x hx2 with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact neg_mem (one_mem _)
    · have hdual : (m : ℂ) • v ∈ dualLat (stdH B.L (Fin 4 × D.what₂.Tau))
          (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) := by
        rw [sd.selfDual]
        exact hmv
      obtain ⟨k, hk⟩ := hdual x hx2
      have hk' : (m : ℂ) * (altE (stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ) = (k : ℂ) := by
        have e : altE (stdH B.L (Fin 4 × D.what₂.Tau)) ((m : ℂ) • v) x
            = (m : ℝ) * altE (stdH B.L (Fin 4 × D.what₂.Tau)) v x := by
          simp only [altE, map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_im, Complex.natCast_re,
            Complex.natCast_im, zero_mul, add_zero]
        rw [e] at hk
        exact_mod_cast hk
      refine rootOfUnity_mem_Qbar (k := 2 * m) (Nat.mul_pos two_pos hm) ?_
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨-k, ?_⟩
      push_cast
      linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hk'

  let T0 : Finset ℂ := insert B.kappa⁻¹ (S.image r ∪ (Finset.univ ×ˢ Finset.univ).image
    (fun p : (Fin 4 × D.what₂.Tau) × (Fin 4 × D.what₂.Tau) =>
      LinearMap.toMatrix' (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) p.1 p.2))
  have hT0 : ∀ y ∈ T0, y ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact inv_mem (mem_algebraicClosure_iff.2 (kapAlg_all B))
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact hrQ x hx
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
      exact gC_mat_mem B p.1 p.2
  obtain ⟨M0, hM0f, hM0⟩ := exists_nf T0 hT0
  let Mh : (Fin 4 × D.what₂.Tau → ℂ) → (Fin 4 × D.what₂.Tau) → IntermediateField ℚ ℂ := fun x w =>
    if h : ∃ N : ℕ, 0 < N ∧ (N : ℂ) * (v w + x w) ∈ B.L.lattice then (h1 _ h).choose else ⊥
  have hMhf : ∀ x w, FiniteDimensional ℚ (Mh x w) := by
    intro x w
    by_cases h : ∃ N : ℕ, 0 < N ∧ (N : ℂ) * (v w + x w) ∈ B.L.lattice
    · have e : Mh x w = (h1 _ h).choose := dif_pos h
      rw [e]
      exact (h1 _ h).choose_spec.1
    · have e : Mh x w = ⊥ := dif_neg h
      rw [e]
      infer_instance
  let M : IntermediateField ℚ ℂ := M0 ⊔ ⨆ x : {x // x ∈ S}, ⨆ w : Fin 4 × D.what₂.Tau, Mh x.1 w
  have hMf : FiniteDimensional ℚ M := by
    have : FiniteDimensional ℚ (⨆ x : {x // x ∈ S}, ⨆ w : Fin 4 × D.what₂.Tau, Mh x.1 w : IntermediateField ℚ ℂ) :=
      finite_iSup _ fun x => finite_iSup _ fun w => hMhf x.1 w
    exact IntermediateField.finiteDimensional_sup M0 _
  have hM0le : M0 ≤ M := le_sup_left
  have hMhle : ∀ x ∈ S, ∀ w, Mh x w ≤ M := fun x hx w =>
    le_trans (le_trans (le_iSup (fun w => Mh x w) w)
      (le_iSup (fun y : {x // x ∈ S} => ⨆ w : Fin 4 × D.what₂.Tau, Mh y.1 w) ⟨x, hx⟩)) le_sup_right
  have hcoef : ∀ x ∈ S, ∀ w, CoefIn1 (f x w) M := by
    intro x hx w k
    have h := htor x hx w
    have e : Mh x w = (h1 _ h).choose := dif_pos h
    have hk := (h1 _ h).choose_spec.2 k
    rw [← e] at hk
    exact hMhle x hx w hk
  have hfan : ∀ x w, AnalyticOnNhd ℂ (f x w) Set.univ := fun x w => translation_operator_analytic B.L _ hthd
  have hfd : ∀ x w, Differentiable ℂ (f x w) := by
    intro x w z
    exact ((hfan x w) z (Set.mem_univ _)).differentiableAt
  have hGc := coefInMv_sum S r (fun x => Formalism.L2.Th1.H.prodFn (f x)) (fun x => prodFn_analytic (f x) (hfd x)) M
    (fun x hx => hM0le (hM0 _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem r hx)))))
    (fun x hx => coefInMv_prodFn M (f x) (fun w => hfan x w 0 (Set.mem_univ _)) (hcoef x hx))
  have hmat : ∀ i j, LinearMap.toMatrix' (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) i j ∈ M :=
    fun i j => hM0le (hM0 _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(i, j), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩))))
  have hGcomp := coefInMv_comp_lin G (hGc.2 0 (Set.mem_univ _))
    (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) M hmat hGc.1
  have hGan : AnalyticAt ℂ (fun z => G (B.gC z)) 0 := by
    have hl := (LinearMap.toContinuousLinearMap
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))).analyticAt 0
    exact AnalyticAt.comp (g := G) (hGc.2 _ (Set.mem_univ _)) hl
  refine ⟨M, hMf, ?_⟩
  rw [hT]
  intro ν
  rw [(Formalism.L2.Th1.H.taylorMvLinear _ (fun z => G (B.gC z)) (fun z => G (B.gC z)) hGan hGan).2 B.kappa⁻¹,
    MvPowerSeries.coeff_C_mul]
  exact mul_mem (hM0le (hM0 _ (Finset.mem_insert_self _ _))) (hGcomp ν)

theorem kerTransAll_of (h : PeriodTranscendenceAllLattices) : KerTransAll :=
  fun D cc δ B hcc hδ => kerTransAlg_of B hcc hδ (h D cc δ B hcc hδ)

end Main

end AlgP

end Formalism.L2.KerInert
