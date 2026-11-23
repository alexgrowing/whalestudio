import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LocEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermAutomorphy
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinCentralLieAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinContinuousLeftAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RayClassGroupFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCharacterSeparation
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinNormEqAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep

namespace UpperTheory.V.Sd.Eis

private def Rel {G : Type} [Group G] (φ ψ : G → ℂ) : Prop :=
  ∃ Λ : (G → ℂ) →ₗ[ℂ] (G → ℂ), ∀ h, Λ (fun g => φ (g * h)) = fun g => ψ (g * h)

private theorem Rel.scal {G : Type} [Group G] {φ ψ : G → ℂ} (h : Rel φ ψ) {k : G} {z : ℂ} (hk : ∀ g, φ (g * k) = z * φ g) (g : G) :
    ψ (g * k) = z * ψ g := by
  obtain ⟨Λ, hΛ⟩ := h
  have e : (fun g => φ (g * k)) = z • fun g => φ (g * 1) := by funext g; simp [hk]
  have := hΛ k
  rw [e, map_smul, hΛ] at this
  simpa using (congrFun this g).symm

section Aff
variable {R S : Type} [CommRing R] [CommRing S]

private theorem aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem corner_aff (s : R →ₙ+* S) (y : Rˣ) (x : R) : cornerGL 2 s (aff y x) = aff (Units.map (corner s) y) (s x) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (aff y x i j) = _
  fin_cases i <;> fin_cases j <;> simp [aff, corner]

private theorem corner_scalar (s : R →ₙ+* S) (y : Rˣ) : cornerGL 2 s (Matrix.GeneralLinearGroup.scalar (Fin 2) y) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) y) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) +
    s (Matrix.GeneralLinearGroup.scalar (Fin 2) y i j) = _
  fin_cases i <;> fin_cases j <;> simp [corner, Matrix.GeneralLinearGroup.scalar]

private theorem det_aff (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext; simp [aff, Matrix.det_fin_two]

private theorem scalar_comm (y : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) y = Matrix.GeneralLinearGroup.scalar (Fin 2) y * g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

private theorem continuous_aff [TopologicalSpace R] [IsTopologicalRing R] : Continuous fun y : Rˣ => aff y (0 : R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop

end Aff

variable {F : Type} [Field F] [NumberField F]

private theorem ct_rel [MeasurableSpace (NA F)] (μ : Measure (NA F)) (D : Set (NA F)) (φ : GA F 2 → ℂ)
    (h : ∀ g, IntegrableOn (fun x : NA F => φ (unip x * g)) D μ) : Rel φ (cterm μ D φ) := by
  let P : Submodule ℂ (GA F 2 → ℂ) :=
    { carrier := {θ | ∀ g, IntegrableOn (fun x : NA F => θ (unip x * g)) D μ}
      add_mem' := fun ha hb g => (ha g).add (hb g)
      zero_mem' := fun g => integrable_zero _ _ _
      smul_mem' := fun c θ hθ g => (hθ g).const_mul c }
  let L : P →ₗ[ℂ] (GA F 2 → ℂ) :=
    { toFun := fun θ => cterm μ D θ.1
      map_add' := fun a b => funext fun g => integral_add (a.2 g) (b.2 g)
      map_smul' := fun c a => funext fun g => integral_const_mul c _ }
  obtain ⟨Λ, hΛ⟩ := L.exists_extend
  refine ⟨Λ, fun k => ?_⟩
  have hk : (fun g => φ (g * k)) ∈ P := fun g => by simpa only [mul_assoc] using h (g * k)
  refine (LinearMap.congr_fun hΛ ⟨_, hk⟩).trans (funext fun g => ?_)
  simp only [L, cterm, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]

private theorem ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

variable [IsTotallyReal F]

private theorem ct_arch {ψ : GA F 2 → ℂ} {k : ℕ} (h : ∀ (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ),
    (∀ t v, (y t).val v = Real.exp (t * u v)) → ∀ g,
    HasDerivAt (fun t => ψ (TR.infGL F 2 (aff (y t) 0) * g)) ((k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ) * ψ g) 0)
    (y : (TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (g : GA F 2) :
    ψ (aff (TR.infId F y) 0 * g) = (((∏ v, y.val v) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ψ g := by
  let u : TR.Rinf F := fun v => Real.log (y.val v)
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun v => Real.exp (t * u v), fun v => Real.exp (-(t * u v)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have h1 : z 1 = y := Units.ext (funext fun v => by simp [z, u, Real.exp_log (hy v)])
  have := ode (f := fun t => ψ (TR.infGL F 2 (aff (z t) 0) * g)) (κ := (k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ)) fun t => by
    have h2 := h u z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, aff_mul, ← hz]; simp
  rw [h1, h0, aff_one, map_one, one_mul, TR.infGL, corner_aff, map_zero] at this
  refine this.trans ?_
  congr 1
  rw [Real.rpow_def_of_pos (Finset.prod_pos fun v _ => hy v), Real.log_prod (fun v _ => (hy v).ne')]
  push_cast
  congr 1; simp [u]; ring

private theorem proj (hR : RayFin) (hC : CharPick) {φ : TR.Sm F 2} {ψ : GA F 2 → ℂ} (hl : IsOpen {k | TR.finRep F 2 k φ = φ})
    (h0 : ψ ≠ 0) (hr : Rel φ.1 ψ) (hN : ∀ x g, ψ (aff 1 x * g) = ψ g) (ν : HChar F)
    (hT : ∀ a : Fˣ, ∀ g, ψ (aff (diagUnits F a) 0 * g) = ψ g)
    (hI : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ g, ψ (aff (TR.infId F y) 0 * g) = ((ν.1 (TR.infId F y) : ℂˣ) : ℂ) * ψ g) :
    ∃ (η : HChar F) (Ψ : GA F 2 → ℂ), IsOfFinOrder η ∧ Ψ ≠ 0 ∧ Rel φ.1 Ψ ∧
      ∀ a x g, Ψ (aff a x * g) = (((η * ν).1 a : ℂˣ) : ℂ) * Ψ g := by
  let f : GA F 2 → Ideles F → ℂ := fun g t => ((ν.1 t⁻¹ : ℂˣ) : ℂ) * ψ (aff t 0 * g)
  let H : GA F 2 → Subgroup (Ideles F) := fun g =>
    { carrier := {u | ∀ t, f g (t * u) = f g t}
      one_mem' := fun t => by rw [mul_one]
      mul_mem' := fun {a b} ha hb t => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha t => by rw [← ha, inv_mul_cancel_right] }
  have am : ∀ t u : Ideles F, aff (t * u) (0 : Ad F) = aff u 0 * aff t 0 := fun t u => by rw [aff_mul, mul_comm]; simp
  have hH : ∀ g, IsOpen (H g : Set (Ideles F)) ∧ (H g).FiniteIndex := fun g => by
    refine hR F (H g) (fun a t => ?_) (fun y hy t => ?_) ?_
    · simp only [f, am, mul_assoc, hT, mul_inv, map_mul, map_inv, ν.2.2 a, inv_one, mul_one]
    · simp only [f, am, mul_assoc, hI y hy, mul_inv, map_mul, map_inv, Units.val_mul, Units.inv_mul_cancel_left]
    · set k := Matrix.GeneralLinearGroup.map (pFin F) g
      have h1 := (isOpen_ker_finIdele F (ν.1.comp (finId F)) (ν.2.1.comp (continuous_finId F))).mem_nhds (map_one _)
      have h2 := (hl.preimage (f := fun u : (Af F)ˣ => k⁻¹ * aff u 0 * k)
        ((continuous_const.mul continuous_aff).mul continuous_const)).mem_nhds (x := 1) (by simp [aff_one])
      filter_upwards [h1, h2] with u hu1 hu2 t
      have e : aff (finId F u) 0 * g = g * finGL F 2 (k⁻¹ * aff u 0 * k) := by
        have : aff (finId F u) 0 = finGL F 2 (aff u 0) := by rw [finGL, corner_aff, map_zero]; rfl
        rw [this]
        exact TR.ga_ext (by simp) (by simp [k, mul_assoc])
      have e2 := hr.scal (k := finGL F 2 (k⁻¹ * aff u 0 * k)) (z := 1) fun x => by
        rw [one_mul]; exact congrFun (congrArg Subtype.val hu2) x
      have hu3 : ν.1 (finId F u) = 1 := hu1
      simp only [f]
      rw [mul_comm t, am, mul_assoc, e, ← mul_assoc, e2]
      simp [hu3]
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 h0
  obtain ⟨χ, L, hχ, hL0, hL⟩ := hC _ (H g₀) (hH g₀).2 (f g₀)
    (Function.ne_iff.2 ⟨1, by simpa [f, aff_one] using hg₀⟩) fun t u hu => hu t
  have hc : Continuous χ := continuous_of_continuousAt_one χ <| (continuousAt_const (y := 1)).congr <|
    Filter.eventually_of_mem ((hH g₀).1.mem_nhds (one_mem _)) fun u hu => (hχ u hu).symm
  have hd : ∀ a : Fˣ, χ (diagUnits F a) = 1 := fun a => hχ _ fun t => by
    simp only [f, am, mul_assoc, hT, mul_inv, map_mul, map_inv, ν.2.2 a, inv_one, mul_one]
  refine ⟨⟨χ, hc, hd⟩, fun g => L (f g), ?_, Function.ne_iff.2 ⟨g₀, hL0⟩, ?_, fun a x g => ?_⟩
  · have := (hH g₀).2
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨(H g₀).index, Nat.pos_of_ne_zero this.index_ne_zero, Subtype.ext (MonoidHom.ext fun t => ?_)⟩
    change χ t ^ _ = 1
    rw [← map_pow]
    exact hχ _ (Subgroup.pow_index_mem _ t)
  · obtain ⟨Λ, hΛ⟩ := hr
    let M : (GA F 2 → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) :=
      { toFun := fun θ g => L fun t => ((ν.1 t⁻¹ : ℂˣ) : ℂ) * θ (aff t 0 * g)
        map_add' := fun a b => funext fun g => by
          rw [Pi.add_apply, ← map_add]; congr 1; funext t; simp [mul_add]
        map_smul' := fun c a => funext fun g => by
          rw [Pi.smul_apply, ← map_smul]; congr 1; funext t; simp [mul_left_comm] }
    refine ⟨M ∘ₗ Λ, fun h => ?_⟩
    rw [LinearMap.comp_apply, hΛ]
    funext g
    simp only [M, f, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  · have e : f (aff a x * g) = ((ν.1 a : ℂˣ) : ℂ) • fun t => f g (t * a) := by
      funext t
      have : aff t (0 : Ad F) * (aff a x * g) = aff 1 (t * x) * (aff (t * a) 0 * g) := by
        rw [← mul_assoc, ← mul_assoc, aff_mul, aff_mul]; simp
      simp only [f, this, hN, Pi.smul_apply, smul_eq_mul, mul_inv, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    change L _ = ((χ a * ν.1 a : ℂˣ) : ℂ) * _
    rw [e, map_smul, hL (H g) (hH g).2 _ (fun t u hu => hu t), Units.val_mul, smul_eq_mul]; ring

private theorem loc {φ : TR.Sm F 2} {Ψ : GA F 2 → ℂ} (h0 : Ψ ≠ 0) (hr : Rel φ.1 Ψ) (w : Pl F) (c : ℕ) (lam : ℂ)
    (hf : φ ∈ Hi.fixd (locSm F w) (K1 w c)) (he : Uop w (locSm F w) c φ = lam • φ) :
    ∃ g' : GA F 2, let Φ := fun h => Ψ (finGL F 2 (locGL F 2 w h) * g')
      Φ ≠ 0 ∧ Φ ∈ Hi.fixd (Hi.rtr ℂ _ ℂ) (K1 w c) ∧ Uop w (Hi.rtr ℂ _ ℂ) c Φ = lam • Φ := by
  classical
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 h0
  obtain ⟨Λ, hΛ⟩ := hr
  set k := Matrix.GeneralLinearGroup.map (pFin F) g₀ with hk
  set g' := (finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.map (pLoc F w) k)))⁻¹ * g₀ with hg'
  have hc : ∀ h, g' * finGL F 2 (locGL F 2 w h) = finGL F 2 (locGL F 2 w h) * g' := fun h =>
    TR.ga_ext (by simp) (by simpa [hg', ← hk] using GlobalTheory.CuspRep.LocUniq.comm_locGL w (GlobalTheory.CuspRep.LocEx.map_pLoc_inv_mul w k) h)
  refine ⟨g', ?_⟩
  intro Φ
  let M : TR.Sm F 2 →ₗ[ℂ] (GL (Fin 2) (w.adicCompletion F) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun h => finGL F 2 (locGL F 2 w h) * g') ∘ₗ Λ ∘ₗ (TR.Sm F 2).subtype
  have hM : ∀ h, M (locSm F w h φ) = Hi.rtr ℂ _ ℂ h Φ := fun h => by
    funext x
    refine (congrFun (hΛ (finGL F 2 (locGL F 2 w h))) _).trans ?_
    simp only [Φ, Hi.rtr_apply, map_mul, mul_assoc, hc]
  have hM1 : M φ = Φ := by simpa using hM 1
  have hΦ : Φ ∈ Hi.fixd (Hi.rtr ℂ _ ℂ) (K1 w c) := fun u hu => by rw [← hM, hf u hu, hM1]
  refine ⟨Function.ne_iff.2 ⟨Matrix.GeneralLinearGroup.map (pLoc F w) k, by simpa [Φ, hg'] using hg₀⟩, hΦ, ?_⟩
  have : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers F)) := inferInstance
  have := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  have hs := IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F)
  have hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image (Function.surjInv hs) : Finset _) : Set (w.adicCompletionIntegers F))
      Set.univ := by
    rw [Finset.coe_image, Finset.coe_univ]
    refine ⟨Set.mapsTo_univ _ _, ?_, fun y _ => ⟨_, ⟨y, trivial, rfl⟩, Function.surjInv_eq hs y⟩⟩
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ e
    rw [Function.surjInv_eq hs, Function.surjInv_eq hs] at e
    rw [e]
  rw [(uopSum F w _ _ c Φ hΦ).2 _ hS, ← hM1, ← map_smul, ← he, (uopSum F w _ _ c φ hf).2 _ hS, map_add, map_sum, hM1]
  simp only [hM, apply_ite M, map_zero]

omit [IsTotallyReal F] in
private theorem ι_aff (w : Pl F) (a : (w.adicCompletion F)ˣ) : Units.map (corner (sFin F)) (Units.map (corner (sLoc F w)) a) =
    localIdele F w a := by
  have := finId_det_locGL w (aff a 0)
  rwa [locGL, corner_aff, det_aff, det_aff] at this

private theorem main (hA : SmCont) (hB : CtBasic) (hL : CtLeft) (hR : RayFin) (hC : CharPick) (hν : AbsPow) : HolEis := by
  intro F _ _ _ k hk c _ ω hω φ lam hφ hcusp
  have hn : ¬ IsCuspidal φ.1 := fun h => hcusp ⟨hφ.hol.aut, h⟩
  unfold IsCuspidal at hn
  push Not at hn
  obtain ⟨r, h0, h1, _, _, μ, D, hμ, hD, g₀, hg₀⟩ := hn
  obtain rfl : r = 1 := by omega
  obtain ⟨hi, hN, hT⟩ := hB F μ D hD φ.1 (hA F 2 φ hφ.hol.aut.level) hφ.hol.aut.left
  obtain ⟨ν, hν1, hν2⟩ := hν F ((k : ℝ) / 2)
  obtain ⟨η, Ψ, hη, hΨ0, hr, hΨ⟩ := proj hR hC hφ.hol.aut.level (Function.ne_iff.2 ⟨g₀, hg₀⟩) (ct_rel μ D φ.1 hi) hN ν hT
    fun y hy g => by rw [hν1 y hy]; exact ct_arch (hL F μ D hD k c ω hω φ hφ.hol) y hy g
  have hZ : ∀ z g, Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * Ψ g := fun z g => by
    rw [← scalar_comm]
    exact hr.scal (fun g => by rw [scalar_comm, hφ.hol.cent]) g
  have key : ∀ w : Pl F, ∃ lam' : ℂ, lam w = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) * lam' ∧
      (c w = 0 → (∀ x, IsUnitAt w x → (η * ν).loc w x = 1 ∧ (ω * η⁻¹ * ν⁻¹).loc w x = 1) ∧
        lam' = (normV w : ℂ) * ((η * ν).val w : ℂˣ) + ((ω * η⁻¹ * ν⁻¹).val w : ℂˣ)) ∧
      (c w ≠ 0 → lam' = 0 ∨ ((∀ x, IsUnitAt w x → (η * ν).loc w x = 1) ∧ lam' = (normV w : ℂ) * ((η * ν).val w : ℂˣ)) ∨
        ((∀ x, IsUnitAt w x → (ω * η⁻¹ * ν⁻¹).loc w x = 1) ∧ lam' = ((ω * η⁻¹ * ν⁻¹).val w : ℂˣ))) := fun w => by
    have hq : (0 : ℝ) < normV w := by
      have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
      exact_mod_cast Nat.card_pos (α := 𝓞 F ⧸ w.asIdeal)
    have hq' : (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hq _).ne'
    refine ⟨_⁻¹ * lam w, (mul_inv_cancel_left₀ hq' _).symm, ?_⟩
    obtain ⟨g', h1, h2, h3⟩ := loc hΨ0 hr w (c w) _ (hφ.hol.level w)
      ((eq_inv_smul_iff₀ hq').2 (hφ.eig w) |>.trans (smul_smul _ _ _))
    refine locEig F w ((η * ν).loc w) ((ω * η⁻¹ * ν⁻¹).loc w) ℂ _ h1 (fun a d x g => ?_) _ _ h2 h3
    simp only [map_mul, mul_assoc]
    rw [locGL, corner_scalar, corner_aff, finGL, corner_scalar, corner_aff, ι_aff, ι_aff, hZ, hΨ, ← mul_assoc, ← Units.val_mul, smul_eq_mul]
    congr 2
    change ω.loc w d * (η * ν).loc w (a / d) = _
    simp only [HChar.loc_mul, HChar.loc_inv, div_eq_mul_inv, map_mul, map_inv, mul_inv]
    ac_rfl
  refine ⟨η, ω * η⁻¹, hη, hω.mul hη.inv, by rw [mul_comm, inv_mul_cancel_right], ?_⟩
  have num : ∀ w : Pl F, (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) * ((normV w : ℂ) * ((η * ν).val w : ℂˣ)) = (η.val w : ℂˣ) ∧
      (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) * ((ω * η⁻¹ * ν⁻¹).val w : ℂˣ) =
        ((ω * η⁻¹).val w : ℂˣ) * (normV w : ℂ) ^ (k - 1) := fun w => by
    have hq : (0 : ℝ) < normV w := by
      have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
      exact_mod_cast Nat.card_pos (α := 𝓞 F ⧸ w.asIdeal)
    have e1 : (normV w : ℝ) ^ ((k : ℝ) / 2 - 1) * normV w * (normV w : ℝ) ^ (-((k : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add_one hq.ne', ← Real.rpow_add hq]; simp
    have e2 : (normV w : ℝ) ^ ((k : ℝ) / 2 - 1) * ((normV w : ℝ) ^ (-((k : ℝ) / 2)))⁻¹ = (normV w : ℝ) ^ (k - 1) := by
      rw [← Real.rpow_neg hq.le, ← Real.rpow_add hq, ← Real.rpow_natCast, Nat.cast_sub hk]; congr 1; push_cast; ring
    have e1' := congrArg (fun x : ℝ => (x : ℂ)) e1
    have e2' := congrArg (fun x : ℝ => (x : ℂ)) e2
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_pow] at e1' e2'
    rw [HChar.val_mul, HChar.val_mul (ω * η⁻¹), HChar.val_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, (hν2 w).2]
    constructor
    · linear_combination ((η.val w : ℂˣ) : ℂ) * e1'
    · linear_combination (((ω * η⁻¹).val w : ℂˣ) : ℂ) * e2'
  have u1 : ∀ (w : Pl F) x, IsUnitAt w x → (η * ν).loc w x = 1 → η.loc w x = 1 := fun w x hx h => by
    rwa [HChar.loc_mul, (hν2 w).1 x hx, mul_one] at h
  have u2 : ∀ (w : Pl F) x, IsUnitAt w x → (ω * η⁻¹ * ν⁻¹).loc w x = 1 → (ω * η⁻¹).loc w x = 1 := fun w x hx h => by
    rwa [HChar.loc_mul, HChar.loc_inv, (hν2 w).1 x hx, inv_one, mul_one] at h
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨l, e, h, -⟩ := key w
    obtain ⟨h1, h2⟩ := h hw
    exact ⟨fun x hx => u1 w x hx (h1 x hx).1, fun x hx => u2 w x hx (h1 x hx).2, by rw [e, h2, mul_add, (num w).1, (num w).2]⟩
  · obtain ⟨l, e, -, h⟩ := key w
    rcases h hw with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [e, h, mul_zero])
    · exact Or.inr (Or.inl ⟨fun x hx => u1 w x hx (h1 x hx), by rw [e, h2, (num w).1]⟩)
    · exact Or.inr (Or.inr ⟨fun x hx => u2 w x hx (h1 x hx), by rw [e, h2, (num w).2]⟩)

end UpperTheory.V.Sd.Eis

theorem UpperTheory.V.Sd.holEis :
    UpperTheory.V.Sd.HolEis :=
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  UpperTheory.V.Sd.Eis.main UpperTheory.eisenstein_smooth_continuous hB
    (UpperTheory.eisenstein_continuous_left_action UpperTheory.eisenstein_smooth_continuous hB (UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock) UpperTheory.eisenstein_lie_algebra_action UpperTheory.eisenstein_central_lie_action)
    UpperTheory.ray_class_group_finite UpperTheory.exists_character_separation UpperTheory.eisenstein_norm_eq_abs_pow
