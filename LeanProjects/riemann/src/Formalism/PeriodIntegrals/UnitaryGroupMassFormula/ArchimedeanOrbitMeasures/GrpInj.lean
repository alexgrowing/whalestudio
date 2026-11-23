import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix NNReal

theorem injOn_nhds_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hinj : Function.Injective f') : ∃ s ∈ 𝓝 a, InjOn f s := by
  obtain ⟨K, hK, hanti⟩ := (f' : E →ₗ[ℝ] F).injective_iff_antilipschitz.mp hinj
  have hc : (0 : ℝ≥0) < (2 * K)⁻¹ := by
    apply inv_pos.2
    exact mul_pos (by norm_num) hK
  obtain ⟨s, hs, hap⟩ := hf.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (Or.inr hc)
  refine ⟨s, hs, fun x hx y hy hxy => ?_⟩
  have h1 : ‖f x - f y - f' (x - y)‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖ := hap x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 : dist x y ≤ K * dist (f' x) (f' y) := hanti.le_mul_dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h3 : ‖x - y‖ ≤ ‖x - y‖ / 2 := by
    calc ‖x - y‖ ≤ K * ‖f' (x - y)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 hK'.le
      _ = ‖x - y‖ / 2 := by
        push_cast
        field_simp
  have : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

set_option backward.isDefEq.respectTransparency false in

theorem exp_mul_injOn {ι V : Type} [Fintype ι] [Fintype V] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)) (P : V → Matrix (Fin n) (Fin n) ℂ)
    (hker : ∀ x, (∀ v, L x v * P v = 0) → x = 0) :
    ∃ r : ℝ, 0 < r ∧ InjOn (fun x => fun v => NormedSpace.exp (L x v) * P v) (ball 0 r) := by
  open scoped Matrix.Norms.Operator in
  let Lc : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) := L.toContinuousLinearMap
  let R : V → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    fun v => (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip (P v)
  let f' : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    ContinuousLinearMap.pi fun v => (R v).comp ((ContinuousLinearMap.proj v).comp Lc)
  have hf' : ∀ x v, f' x v = L x v * P v := fun x v => rfl
  have hd : HasStrictFDerivAt (fun x => fun v => NormedSpace.exp (L x v) * P v) f' 0 := by
    rw [hasStrictFDerivAt_pi]
    intro v
    have h0 : HasStrictFDerivAt (fun x : EuclideanSpace ℝ ι => L x v)
        ((ContinuousLinearMap.proj v).comp Lc) 0 :=
      ((ContinuousLinearMap.proj v).comp Lc).hasStrictFDerivAt
    have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L 0 v) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    have h2 := (R v).hasStrictFDerivAt.comp 0 (he.comp 0 h0)
    convert h2 using 1
    · funext x
      rfl
    · exact ContinuousLinearMap.ext fun x => rfl
  have hinj : Function.Injective f' := by
    intro x y hxy
    have : x - y = 0 := hker (x - y) fun v => by
      have := congrFun (congrArg (fun g => g) (show f' (x - y) = 0 by rw [map_sub, hxy, sub_self])) v
      rwa [hf'] at this
    exact sub_eq_zero.1 this
  obtain ⟨s, hs, hsi⟩ := injOn_nhds_of_strict hd hinj
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  exact ⟨r, hr, hsi.mono hrs⟩

theorem toInf_injective {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    Function.Injective (X.toInf hb) := by
  intro s t h
  have e := PI.AprimeInfU.eq_of_ofHA X hb ((s, 1) : X.B.I.GA) ((t, 1) : X.B.I.GA)
    (PI.AprimeInfU.ofHAInf_congr X _ _ h)
    (PI.AprimeInfU.ofHAFin_congr X _ _ (by rw [PI.AprimeInfU.toHA_fin_one X hb s, PI.AprimeInfU.toHA_fin_one X hb t]))
  exact congrArg Prod.fst e

def toInfHom {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    X.B.I.Ginf →* HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  MonoidHom.mk' (X.toInf hb) (PI.AprimeInfU.toInf_mul X hb)

theorem lie_zero_of_cols {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hL : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) (hB : ∀ i ∈ S, ∀ j ∈ S, M i j = 0)
    (hC : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0) : M = 0 := by
  have hcol : ∀ r s, s ∉ S → M r s = 0 := by
    intro r s hs
    have := congrFun (congrFun hC r) s
    rw [Matrix.mul_diagonal] at this
    simpa [hs] using this
  ext r s
  by_cases hs : s ∈ S
  · by_cases hr : r ∈ S
    · exact hB r hr s hs
    · have h := congrFun (congrFun hL s) r
      simp only [Formalism.REAL.Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.conjTranspose_apply, Matrix.zero_apply, hcol s r hr, mul_zero, add_zero] at h
      have hd : (if ε r = true then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have := (mul_eq_zero.1 h).resolve_right hd
      simpa using this
  · exact hcol r s hs

theorem grpInj_holds : GrpInj := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  have hc := ctx.2.1
  have hL := ctx.2.2.1
  have hB := ctx.2.2.2
  set P : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ :=
    fun v => Matrix.diagonal (fun k => if k ∈ S v then (0 : ℂ) else 1) with hP
  have hnorm : ∀ {κ' : Type} [Fintype κ'] (x : EuclideanSpace ℝ κ')
      (M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ),
      M = 0 → ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 = ‖x‖ ^ 2 → x = 0 := by
    intro κ' _ x M hM h
    subst hM
    simp only [Pi.zero_apply, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h.symm)
  obtain ⟨r1, hr1, hi1⟩ := exp_mul_injOn L P fun x hx => by
    refine hnorm x (L x) (funext fun v => lie_zero_of_cols (X.B.I.ε v) (S v) _ (hL.1 x v).1 (hL.1 x v).2 (hx v))
      (hL.2.1 x)
  obtain ⟨r2, hr2, hi2⟩ := exp_mul_injOn L₁ (fun _ => 1) fun x hx => by
    refine hnorm x (L₁ x) (funext fun v => by simpa using hx v) (hB.2.1 x)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun a ha b hb' hm => ?_, fun y hy y' hy' he => ?_⟩
  ·
    have e1 : (kap0 X hb c L a)⁻¹ * kap0 X hb c L b =
        X.toInf hb (c * ((fun v => expU (X.B.I.ε v) (L a v))⁻¹ * (fun v => expU (X.B.I.ε v) (L b v))) * c⁻¹) := by
      unfold kap0
      change (toInfHom X hb _)⁻¹ * toInfHom X hb _ = toInfHom X hb _
      rw [← map_inv, ← map_mul]
      congr 1
      group
    rw [e1] at hm
    have hstd := (hc.2 _).1 hm
    apply hi1 (ball_subset_ball (min_le_left _ _) ha) (ball_subset_ball (min_le_left _ _) hb')
    funext v
    have hv := hstd v
    set u := expU (X.B.I.ε v) (L a v) with hu
    set w := expU (X.B.I.ε v) (L b v) with hw
    have hcol : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v = P v := by
      ext j i
      simp only [hP, Matrix.mul_diagonal, Matrix.diagonal_apply]
      by_cases hi : i ∈ S v
      · by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji, hi]
      · have := hv i hi j
        simp only [Pi.mul_apply, Pi.inv_apply] at this
        rw [this]
        by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji]
    have ea : NormedSpace.exp (L a v) = (((u : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 a v).1).symm
    have eb : NormedSpace.exp (L b v) = (((w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 b v).1).symm
    show NormedSpace.exp (L a v) * P v = NormedSpace.exp (L b v) * P v
    rw [ea, eb]
    set U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (u : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hU
    set W : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (w : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hW
    have e4 : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) =
        ((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := rfl
    rw [e4] at hcol
    calc (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v
        = (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
            (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v) := by rw [hcol]
      _ = (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  ·
    have e2 := toInf_injective X hb he
    have e3 : ((fun v => expU (X.B.I.ε v) (L₁ y v)) : X.B.I.Ginf) = fun v => expU (X.B.I.ε v) (L₁ y' v) := by
      simpa using e2
    apply hi2 (ball_subset_ball (min_le_right _ _) hy) (ball_subset_ball (min_le_right _ _) hy')
    funext v
    have := congrArg (fun g : X.B.I.Ginf => (((g v : Formalism.REAL.UJ (X.B.I.ε v)) :
      (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) e3
    rw [expU_val _ _ (hB.1 y v).1, expU_val _ _ (hB.1 y' v).1] at this
    show NormedSpace.exp (L₁ y v) * 1 = NormedSpace.exp (L₁ y' v) * 1
    rw [this]

end PI.AprimeInfW
