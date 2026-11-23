import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory

namespace GlobalTheory.RealPar.Cover

variable {p q n : ℕ} {T : GrpData p q}

theorem ext_of {x y : T.G} (h1 : T.cov x = T.cov y) (h2 : T.sq x = T.sq y) : x = y :=
  T.emb.injective (Prod.ext h1 h2)

theorem norm_sq (x : T.G) : ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, norm_star, norm_pow] at h2
  have h0 : (Jm p q).det * (Jm p q).det = 1 := by rw [← Matrix.det_mul, KStabLie.Jm_sq, Matrix.det_one]
  have h3 : ‖(Jm p q).det‖ ≠ 0 := norm_ne_zero_iff.2 (left_ne_zero_of_mul_eq_one h0)
  have h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4

theorem continuous_sq : Continuous fun x : T.G => ((T.sq x : ℂˣ) : ℂ) :=
  Units.continuous_val.comp (continuous_snd.comp T.emb.continuous)

theorem hasDerivAt_det_exp (X : Mat p q) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
  let e : Ix p q ≃ Fin (p + q) := finSumFinEquiv
  have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
    intro a b
    open scoped Matrix.Norms.Operator in
    have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
    exact h2
  have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Matrix.reindex e e (NormedSpace.exp (t • X)))
    (Matrix.reindex e e X) 0 fun i j => h1 _ _
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv, Matrix.adjugate_one, Matrix.one_mul, Matrix.det_submatrix_equiv_self] at h3
  convert h3 using 1
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact (e.symm.sum_comp fun a => X a a).symm

theorem hasDerivAt_sq {X : Mat p q} (hX : X ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ)) (X.trace / 2) 0 := by
  set f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ) with hf
  have hc : Continuous f := continuous_sq.comp
    (T.expt_cont.comp_continuous (by fun_prop) fun t => KStabLie.smul_mem_upq hX t)
  have h0 : f 0 = 1 := by simp [hf, T.expt_zero]
  have h2 : ∀ t, f t ^ 2 = (NormedSpace.exp (t • X)).det := fun t => by
    rw [hf, T.sq_sq, T.expt_cov _ (KStabLie.smul_mem_upq hX t)]
  have h3 := hasDerivAt_det_exp X
  simp only [← h2] at h3
  rw [hasDerivAt_iff_tendsto_slope] at h3 ⊢
  have h4 : Filter.Tendsto (fun t => f t + 1) (nhdsWithin 0 {0}ᶜ) (nhds 2) := by
    have := (hc.add (continuous_const (y := (1 : ℂ)))).tendsto 0
    rw [Pi.add_apply, h0, one_add_one_eq_two] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (h3.div h4 two_ne_zero).congr' ((h4.eventually_ne two_ne_zero).mono fun t ht => ?_)
  simp only [Pi.div_apply, slope_def_module, h0, Complex.real_smul]
  field_simp
  ring

def twAct {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) :
    Mat p q →ₗ[ℂ] Module.End ℂ V :=
  act - (1 / 2 : ℂ) • (Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight (1 : Module.End ℂ V)

theorem twAct_apply {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (X : Mat p q) (v : V) :
    twAct act X v = act X v - (X.trace / 2) • v := by
  simp [twAct, smul_smul, div_eq_inv_mul]

theorem wtSub_twAct {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    wtSub (twAct act) μ = wtSub act fun a => μ a + 1 / 2 := by
  ext v
  simp [wtSub, twAct_apply, Eab, add_smul, sub_sub, add_comm]

theorem isHW_twAct {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ)
    (v : V) : IsHW (twAct act) μ v ↔ IsHW act (fun a => μ a + 1 / 2) v := by
  have : ∀ a b : Ix p q, posC a b → twAct act (Eab a b) v = act (Eab a b) v := by
    intro a b h
    have hab : a ≠ b := by rintro rfl; cases a <;> simp [posC] at h
    simp [twAct_apply, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]
  simp only [IsHW, hwSub, wtSub_twAct, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun a b h => by rw [this a b h]))

def twMod (M : GKMod p q) : GKMod p q where
  V := M.V
  act := twAct M.act
  lie X Y := by
    ext v
    have := congrArg (fun f : Module.End ℂ M.V => f v) (M.lie X Y)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [twAct_apply, LinearMap.sub_apply, Module.End.mul_apply, this, Matrix.trace_sub,
      Matrix.trace_mul_comm X Y, sub_self, map_sub (M.act X), map_sub (M.act Y), map_smul]
    module
  kfin v := by
    obtain ⟨W, a, b, c⟩ := M.kfin v
    exact ⟨W, a, b, fun X hX w hw => by
      rw [twAct_apply]; exact W.sub_mem (c X hX w hw) (W.smul_mem _ hw)⟩
  wts v := by
    refine (iSup_mono' fun μ => ⟨fun a => μ a - 1 / 2, ?_⟩ :
      (⨆ μ, wtSub M.act μ) ≤ ⨆ μ, wtSub (twAct M.act) μ) (M.wts v)
    simp [wtSub_twAct]

def twURep (U : URep T) : URep T where
  H := U.H
  π := { toFun := fun x => ((T.sq x : ℂˣ) : ℂ)⁻¹ • U.π x
         map_one' := by simp
         map_mul' := fun x y => by simp [smul_smul, mul_comm] }
  isom g x := by simp [norm_smul, norm_sq, U.isom]
  cont x := (continuous_sq.inv₀ fun g => (T.sq g).ne_zero).smul (U.cont x)

def twist (R : DSRep T) : DSRep T where
  U := twURep R.U
  nontriv := R.nontriv
  irred S hS h := R.irred S hS fun g x hx => by
    exact (smul_inv_smul₀ (T.sq g).ne_zero (R.U.π g x)) ▸ S.smul_mem ((T.sq g : ℂˣ) : ℂ) (h g x hx)
  fdeg := R.fdeg
  fdeg_pos := R.fdeg_pos
  schur x y := by
    have h1 : ∀ (x y : R.U.H) (g : T.G),
        ‖(inner ℂ y (((T.sq g : ℂˣ) : ℂ)⁻¹ • R.U.π g x) : ℂ)‖ = ‖(inner ℂ y (R.U.π g x) : ℂ)‖ := fun x y g => by
      simp [inner_smul_right, norm_sq]
    have h2 := R.schur x y
    simp only [← h1 x y] at h2
    exact h2
  HK := twMod R.HK
  ι := R.ι
  ι_inj := R.ι_inj
  ι_range x := by
    refine (R.ι_range x).trans ?_
    change R.U.H at x
    have : Submodule.span ℂ (Set.range fun k : T.Kset => R.U.π k x) =
        Submodule.span ℂ (Set.range fun k : T.Kset => ((T.sq k : ℂˣ) : ℂ)⁻¹ • R.U.π k x) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨k, rfl⟩
        have := Submodule.smul_mem _ ((T.sq k : ℂˣ) : ℂ) (Submodule.subset_span (R := ℂ)
          (Set.mem_range_self (f := fun k : T.Kset => ((T.sq k : ℂˣ) : ℂ)⁻¹ • R.U.π k x) k))
        rwa [smul_inv_smul₀ (T.sq k).ne_zero] at this
      · rintro _ ⟨k, rfl⟩
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact iff_of_eq (congrArg (fun S : Submodule ℂ R.U.H => FiniteDimensional ℂ S) this)
  der X hX v := by
    change R.HK.V at v
    have h1 := ((hasDerivAt_sq (T := T) hX).inv (Units.ne_zero _)).fun_smul (R.der X hX v)
    refine h1.congr_deriv (g' := R.ι (twAct R.HK.act X v)) ?_
    simp [twAct_apply, T.expt_zero, sub_eq_add_neg]

theorem central_scalar (R : DSRep T) {z : T.G} (hz : ∀ x, z * x = x * z) {c : ℂ} {v : R.U.H} (hv : v ≠ 0)
    (h : R.U.π z v = c • v) (w : R.U.H) : R.U.π z w = c • w := by
  have := R.irred (LinearMap.ker ((R.U.π z - c • 1 : R.U.H →L[ℂ] R.U.H) : R.U.H →ₗ[ℂ] R.U.H))
    (ContinuousLinearMap.isClosed_ker _) fun g x hx => by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hx ⊢
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hz, map_mul, ContinuousLinearMap.mul_apply, hx, map_smul]
  rcases this with e | e
  · exact absurd ((Submodule.eq_bot_iff _).1 e v (by simp [h])) hv
  · simpa [sub_eq_zero] using Submodule.eq_top_iff'.1 e w

theorem sq_of_ker {x : T.G} (h : T.cov x = 1) : T.sq x = 1 ∨ T.sq x = -1 := by
  have := T.sq_sq x
  rw [h, Units.val_one, Matrix.det_one, sq_eq_one_iff] at this
  exact this.imp (fun e => Units.ext e) fun e => Units.ext e

theorem trivial_or_twist (R : DSRep T) :
    (∀ x, T.cov x = 1 → R.U.π x = 1) ∨ ∀ x, T.cov x = 1 → (twist R).U.π x = 1 := by
  rw [or_iff_not_imp_left]
  intro h x hx
  rcases sq_of_ker hx with e | e
  · rw [ext_of (x := x) (y := 1) (by rw [hx, map_one]) (by rw [e, map_one]), map_one]
  have hc : ∀ y, x * y = y * x := fun y => ext_of (by simp [hx]) (by simp [mul_comm])
  have h2 : x * x = 1 := ext_of (by simp [hx]) (by simp [e])
  have h3 : ∀ v, R.U.π x v = -v := by
    intro v
    by_contra hv
    refine h fun y hy => ?_
    rcases sq_of_ker hy with e' | e'
    · rw [ext_of (x := y) (y := 1) (by rw [hy, map_one]) (by rw [e', map_one]), map_one]
    rw [ext_of (hy.trans hx.symm) (e'.trans e.symm)]
    ext w
    have := central_scalar R hc (c := 1) (v := R.U.π x v + v) (fun h0 => hv (eq_neg_of_add_eq_zero_left h0))
      (by rw [map_add, ← ContinuousLinearMap.mul_apply, ← map_mul, h2, map_one]; simp [add_comm]) w
    simpa using this
  change ((T.sq x : ℂˣ) : ℂ)⁻¹ • R.U.π x = 1
  ext v
  simp [e, h3]

theorem sum_weight_eq (R : DSRep T) {μ ν : Ix p q → ℚ} {v w : R.HK.V} (hv : IsHW R.HK.act μ v)
    (hw : IsHW R.HK.act ν w) : ∑ a, μ a = ∑ a, ν a := by
  have key : ∀ (θ : ℝ) {μ : Ix p q → ℚ} {v : R.HK.V}, IsHW R.HK.act μ v →
      R.U.π (T.expt (TorusWt.torX fun _ => θ)) (R.ι v) = Complex.exp ((θ * Complex.I) * (∑ a, μ a : ℚ)) • R.ι v := by
    intro θ μ v hv
    apply TorusWt.flow_eq R (TorusWt.torX_mem _)
    have h1 : ∀ a, R.HK.act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
      simpa [wtSub, sub_eq_zero] using hv.2.1
    rw [TorusWt.torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h1, smul_smul, ← Finset.sum_smul, ← Finset.mul_sum]
    push_cast
    rfl
  have cen : ∀ (θ : ℝ) x, T.expt (TorusWt.torX fun _ => θ) * x = x * T.expt (TorusWt.torX fun _ => θ) := by
    intro θ x
    refine ext_of (Units.ext ?_) (by simp [mul_comm])
    simp only [map_mul, Units.val_mul, T.expt_cov _ (TorusWt.torX_mem _)]
    refine Commute.exp_left ?_
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
  have inj : ∀ {v : R.HK.V}, v ≠ 0 → R.ι v ≠ 0 := fun h h0 => h (R.ι_inj (by rw [h0, map_zero]))
  by_contra hne
  have hd : ((∑ a, μ a - ∑ a, ν a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / ((∑ a, μ a - ∑ a, ν a : ℚ) : ℝ) with hθ
  have h1 := (central_scalar R (cen θ) (inj hv.1) (key θ hv) (R.ι w)).symm.trans (key θ hw)
  have h2 := smul_left_injective ℂ (inj hw.1) h1
  have h3 : Complex.exp (Real.pi * Complex.I) = 1 := by
    rw [Complex.exp_eq_exp_iff_exp_sub_eq_one] at h2
    rw [← h2]
    congr 1
    have : (Real.pi : ℂ) = θ * ((∑ a, μ a - ∑ a, ν a : ℚ) : ℝ) := by
      exact_mod_cast (div_mul_cancel₀ _ hd).symm
    rw [this]
    generalize ∑ a, μ a = s
    generalize ∑ a, ν a = t
    push_cast
    ring
  rw [Complex.exp_pi_mul_I] at h3
  norm_num at h3

theorem blattner_add (lam : Ix p q → ℚ) (c : ℚ) : blattner (fun a => lam a + c) = fun a => blattner lam a + c := by
  funext a
  simp only [blattner, rhoNC, add_lt_add_iff_right]
  ring

theorem vogan_add (μ : Ix p q → ℚ) (c : ℚ) :
    vogan (fun a => μ a + c) = vogan μ + 2 * c * ∑ a, μ a + ∑ a : Ix p q, (2 * c * rhoOfIndex a + c ^ 2) := by
  simp only [vogan, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem hasParam_twist (R : DSRep T) (lam : Ix p q → ℚ) :
    HasParam (twist R) lam ↔ HasParam R fun a => lam a + 1 / 2 := by
  have e : ∀ μ v, IsHW (twist R).HK.act μ v ↔ IsHW R.HK.act (fun a => μ a + 1 / 2) v := isHW_twAct R.HK.act
  unfold HasParam
  rw [blattner_add]
  simp only [e]
  refine and_congr_right fun ⟨v, hv⟩ => ⟨fun h μ w hw => ?_, fun h μ w hw => ?_⟩
  · have h1 := h (fun a => μ a - 1 / 2) w (by simpa using hw)
    have h2 := sum_weight_eq R hv hw
    have h3 := vogan_add (fun a => μ a - 1 / 2) (1 / 2)
    simp only [sub_add_cancel, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h2 h3
    rw [vogan_add, h3, Finset.sum_add_distrib]
    linarith
  · have h1 := h _ w hw
    have h2 := sum_weight_eq R hv hw
    rw [vogan_add, vogan_add] at h1
    simp only [Finset.sum_add_distrib] at h1 h2
    linarith

def trivZero (T : GrpData 0 0) : DSRep T where
  U := { H := ℂ, π := 1, isom := fun _ _ => rfl, cont := fun _ => continuous_const }
  nontriv := inferInstanceAs (Nontrivial ℂ)
  irred S _ _ := eq_bot_or_eq_top (α := Submodule ℂ ℂ) S
  fdeg := (T.haar.real Set.univ)⁻¹
  fdeg_pos := by
    have : Finite T.G := Finite.of_injective (β := ({1, -1} : Set ℂˣ))
      (fun x => ⟨T.sq x, sq_of_ker (Units.ext (Subsingleton.elim _ _))⟩)
      fun x y h => ext_of (Units.ext (Subsingleton.elim _ _)) (congrArg Subtype.val h)
    exact inv_pos.2 (ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty) (measure_ne_top _ _))
  schur x y := by
    have : Finite T.G := Finite.of_injective (β := ({1, -1} : Set ℂˣ))
      (fun x => ⟨T.sq x, sq_of_ker (Units.ext (Subsingleton.elim _ _))⟩)
      fun x y h => ext_of (Units.ext (Subsingleton.elim _ _)) (congrArg Subtype.val h)
    change ℂ at x y
    change Integrable (fun _ : T.G => ‖(inner ℂ y x : ℂ)‖ ^ 2) T.haar ∧
      ∫ _ : T.G, ‖(inner ℂ y x : ℂ)‖ ^ 2 ∂T.haar = ‖x‖ ^ 2 * ‖y‖ ^ 2 / (T.haar.real Set.univ)⁻¹
    refine ⟨integrable_const _, ?_⟩
    simp [mul_pow, mul_comm]
  HK := { V := ℂ, act := 0, lie := fun _ _ => by simp,
          kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩,
          wts := fun v => Submodule.mem_iSup_of_mem 0 (by simp [wtSub]) }
  ι := LinearMap.id
  ι_inj := Function.injective_id
  ι_range x := ⟨fun _ => inferInstanceAs (FiniteDimensional ℂ (_ : Submodule ℂ ℂ)), fun _ => ⟨x, rfl⟩⟩
  der X _ v := hasDerivAt_const (0 : ℝ) (show ℂ from v)

end GlobalTheory.RealPar.Cover

end
