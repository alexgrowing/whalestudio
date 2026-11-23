import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatFunDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNonnegFamilyOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumOfDominatedOfEqNearZero
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DoublingSeries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem isMulRightInvariant_haar [m : MeasurableSpace (GL (Fin N) k)] [hm : BorelSpace (GL (Fin N) k)]
    (μ : Measure (GL (Fin N) k)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  borelize k
  have e : m = _ := hm.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := Fin N)).measurable_eq.symm
  subst e
  exact SplitFlip.isMulRightInvariant_of_haar μ

theorem isBorelSph_unique {γ : Fin N → ℂ} {ψ ψ' : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (h' : IsBorelSph k γ ψ') :
    ψ = ψ' := by
  funext g
  obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have ht := fun i => (GlobalTheory.CuspRep.ParLaws.val_diagU ⟨b, hb'⟩ i).symm
  rw [h.1 _ _ hx, h'.1 _ _ hx, h.2 b hb' _ ht, h'.2 b hb' _ ht]

theorem isBorelSph_norm {α β : Fin N → ℂˣ} (hβ : ∀ x, (β x : ℂ) = ((‖(α x : ℂ)‖ : ℝ) : ℂ)) {ψ : GL (Fin N) k → ℂ}
    (h : IsBorelSph k (borelParam (resCard k) α) ψ) :
    IsBorelSph k (borelParam (resCard k) β) fun g => ((‖ψ g‖ : ℝ) : ℂ) := by
  refine ⟨fun g x hx => by simp only [h.1 g x hx], fun b hb t ht => ?_⟩
  have hq : 0 < resCard k := zero_lt_one.trans (one_lt_resCard k)
  simp only [h.2 b hb t ht, norm_prod, norm_zpow, Complex.ofReal_prod, Complex.ofReal_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have e : (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) = ((((i : ℕ) : ℝ) - ((N : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [borelParam, borelParam, hβ, norm_mul, Complex.norm_natCast_cpow_of_pos hq, e, Complex.ofReal_re,
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem zonalInt_norm [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) :
    (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).im = 0 ∧ 0 ≤ (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).re ∧
      ‖zonalInt μK ψ g‖ ≤ (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).re := by
  simp only [zonalInt, integral_complex_ofReal, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨trivial, integral_nonneg fun _ => norm_nonneg _, norm_integral_le_integral_norm _⟩

theorem exists_isZonal_of_form {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (L : X →ₗ[ℂ] ℂ) (hL : ∀ x ∈ K, ∀ u, L (ρ x u) = L u)
    (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → L u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ L w = 1 ∧ GlobalTheory.SmGL.IsZonal π K fun g => L (ρ g w) := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : L w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ L z = 1 ∧ f z ≠ 0 :=
    ⟨(L w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  have hker : LinearMap.ker f.toLinearMap ≤ LinearMap.ker L := fun y hy => by
    have hy0 : f y = 0 := hy
    obtain ⟨y', hy', e⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod L) y fun h hh => by
      refine Prod.ext ?_ (hL h hh y)
      show f (ρ h y) = f y
      rw [f.isIntertwining, hy0, map_zero]
    have hy'' : ∀ x ∈ K, ρ x y' = y' := fun x hx => by simpa using hy' ⟨x, hx⟩
    have e1 : f y' = f y := congrArg Prod.fst e
    have e2 : L y' = L y := congrArg Prod.snd e
    have h1 := hE (y' - L y' • z) (fun x hx => by rw [map_sub, map_smul, hy'' x hx, hz x hx])
      (by rw [map_sub, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
    have h2 := congrArg f (sub_eq_zero.1 h1)
    rw [map_smul, e1, hy0, eq_comm, smul_eq_zero] at h2
    show L y = 0
    rw [← e2]
    exact h2.resolve_right hfz
  let l : Module.Dual ℂ V := (LinearMap.ker f.toLinearMap).liftQ L hker ∘ₗ
    (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl : ∀ y, l (f y) = L y := fun y => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f.toLinearMap).liftQ L hker ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f y)) = _
    rw [this]; rfl
  refine ⟨z, hz, hEz, f z, fun x => ?_, l, fun x => ?_, by rw [hl, hEz], fun g => ?_⟩
  · have := f.isIntertwining _ _ (x : G) z
    rw [hz x x.2] at this
    simpa using this.symm
  · ext v
    obtain ⟨y, rfl⟩ := hf v
    have := f.isIntertwining _ _ (x : G)⁻¹ y
    simp [Module.Dual.transpose_apply, ← this, hl, hL _ (inv_mem x.2)]
  · show L (ρ g z) = _
    rw [← hl, f.isIntertwining]

theorem exists_isZonal_zonalInt [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] (hμ : μK (KO k (Fin N)) = 1) (α : Fin N → ℂˣ)
    (ψ : GL (Fin N) k → ℂ) (hψ : IsBorelSph k (borelParam (resCard k) α) ψ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin N) k) V),
      HasSatake π α ∧ GlobalTheory.SmGL.IsZonal π (KO k (Fin N)) (zonalInt μK ψ) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) α
  refine ⟨_, _, _, π.ρ, hπ, ?_⟩
  obtain ⟨-, hs, S, f, hf⟩ := hπ
  haveI := isMulRightInvariant_haar μK
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := SplitFlip.isOpen_KO.measurableSet
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  have hcont : ∀ u : S.toSubmodule, Continuous u.1.1.1 := fun u => by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x | S.toRepresentation x u = u}) := (hsm u).preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show S.toRepresentation (g⁻¹ * g) u = u by rw [inv_mul_cancel, map_one]; rfl)] with x hx
    have hx' : S.toRepresentation (g⁻¹ * x) u = u := hx
    have h1 : u.1.1.1 (g * (g⁻¹ * x)) = u.1.1.1 g := congrArg (fun z : S.toSubmodule => z.1.1.1 g) hx'
    rwa [mul_inv_cancel_left] at h1
  have hint : ∀ u : S.toSubmodule, IntegrableOn u.1.1.1 (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun u =>
    (hcont u).continuousOn.integrableOn_compact SplitFlip.isCompact_KO
  let L : S.toSubmodule →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK
      map_add' := fun u v => integral_add (hint u) (hint v)
      map_smul' := fun c u => integral_const_mul c _ }
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin N), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin N), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  have hL1 : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin N), S.toRepresentation x u = u) → L u = u.1.1.1 1 := fun u h => by
    show ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK = _
    rw [setIntegral_congr_fun hKm (g := fun _ => u.1.1.1 1) fun x hx => by
      simpa using hr u h 1 x hx]
    simp [Measure.real, hμ]
  have hL : ∀ x ∈ KO k (Fin N), ∀ u, L (S.toRepresentation x u) = L u := fun x hx u => by
    show ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 (κ * x) ∂μK =
      ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK
    rw [← integral_indicator hKm, ← integral_indicator hKm,
      ← integral_mul_right_eq_self ((KO k (Fin N) : Set (GL (Fin N) k)).indicator u.1.1.1) x]
    congr 1
    funext κ
    by_cases h : κ ∈ KO k (Fin N)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mul_mem h hx)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((Subgroup.mul_mem_cancel_right _ hx).1 h')]
  obtain ⟨w, hw, hw1, hz⟩ := exists_isZonal_of_form hsm SplitFlip.isCompact_KO f hf hs L hL fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := (hL1 u h).symm.trans h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  have hw2 : IsBorelSph k (borelParam (resCard k) α) w.1.1.1 := by
    refine ⟨hr w hw, fun b hb t ht => ?_⟩
    have h1 := GlobalTheory.SatakeBound.Rep.law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := (hL1 w hw).symm.trans hw1
    rw [h2, mul_one, mul_one] at h1
    rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [borelParam, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [isBorelSph_unique hψ hw2]
  exact hz

theorem unramified_doubling_sum : GlobalTheory.Published.UnramifiedDoublingGL →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (α : Fin N → ℂˣ) (ρ : ℝ), (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) →
  ∀ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ →
  ∀ s : ℂ, ρ - 1 / 2 < s.re →
    Summable (fun e : {e : Fin N → ℤ // Antitone e} => ‖(μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e))‖) ∧
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} => (μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)))
      (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
  intro H k _ _ _ _ _ N _ _ μK _ hμK ϖ hϖ α ρ hα ψ hψ s hs
  have hq : 1 < resCard k := one_lt_resCard k
  have hq1 : (1 : ℝ) < resCard k := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < resCard k := by linarith
  let β : Fin N → ℂˣ := fun x => Units.mk0 ((‖(α x : ℂ)‖ : ℝ) : ℂ) (by simp)
  have hβ : ∀ x, (β x : ℂ) = ((‖(α x : ℂ)‖ : ℝ) : ℂ) := fun x => rfl
  have hβn : ∀ x, ‖(β x : ℂ)‖ = ‖(α x : ℂ)‖ := fun x => by rw [hβ]; simp
  obtain ⟨ψ', hψ', hM⟩ : ∃ ψ' : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) β) ψ' ∧
      ∀ g, (zonalInt μK ψ' g).im = 0 ∧ 0 ≤ (zonalInt μK ψ' g).re ∧ ‖zonalInt μK ψ g‖ ≤ (zonalInt μK ψ' g).re :=
    ⟨_, isBorelSph_norm hβ hψ, zonalInt_norm μK ψ⟩
  have hZ : ∀ (γ : Fin N → ℂˣ) (φ : GL (Fin N) k → ℂ), IsBorelSph k (borelParam (resCard k) γ) φ →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re → HasSum (fun e : {e : Fin N → ℤ // Antitone e} =>
        (μK.real (cell k (Fin N) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
          zonalInt μK φ (torusElt k (Fin N) ϖ e)))
        (lFactor (resCard k) γ (s + 1 / 2) * lFactor (resCard k) γ⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
    intro γ φ hφ
    obtain ⟨V, _, _, π, hπ, hz⟩ := exists_isZonal_zonalInt μK hμK γ φ hφ
    exact GlobalTheory.Published.UnramifiedDoublingGL.hasSum H k N μK hμK hϖ hπ hz
  let n : {e : Fin N → ℤ // Antitone e} → ℕ := fun e => (sumAbs e.1).toNat
  let wR : {e : Fin N → ℤ // Antitone e} → ℝ := fun e =>
    μK.real (cell k (Fin N) ϖ e) * (resCard k : ℝ) ^ (-((N : ℝ) / 2) * (sumAbs e.1 : ℝ))
  have hw0 : ∀ e, 0 ≤ wR e := fun e => mul_nonneg measureReal_nonneg (Real.rpow_nonneg hq0.le _)
  let b : {e : Fin N → ℤ // Antitone e} → ℂ := fun e => (wR e : ℂ) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)
  let c : {e : Fin N → ℤ // Antitone e} → ℝ := fun e => wR e * (zonalInt μK ψ' (torusElt k (Fin N) ϖ e)).re
  have hterm : ∀ (e : {e : Fin N → ℤ // Antitone e}) (s : ℂ) (u : ℂ),
      (μK.real (cell k (Fin N) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * u) =
        ((wR e : ℂ) * u) * ((resCard k : ℂ) ^ (-s)) ^ n e := by
    intro e s u
    have h := cpow_split hq N s (sumAbs_nonneg e.1)
    rw [h]
    simp only [wR, Complex.ofReal_mul]
    push_cast
    ring
  have hbc : ∀ e, ‖b e‖ ≤ c e := fun e => by
    simp only [b, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 e)]
    exact mul_le_mul_of_nonneg_left (hM _).2.2 (hw0 e)
  have hc0 : ∀ e, 0 ≤ c e := fun e => mul_nonneg (hw0 e) (hM _).2.1
  have hcb : ∀ e, (wR e : ℂ) * zonalInt μK ψ' (torusElt k (Fin N) ϖ e) = (c e : ℂ) := fun e => by
    have h := (hM (torusElt k (Fin N) ϖ e)).1
    simp only [c, Complex.ofReal_mul]
    congr 1
    exact Complex.ext (by simp) (by simp [h])
  have hbα : ∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ := hα
  have hbβ : ∀ x, ‖(β x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(β x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ := fun x => by
    rw [hβn]; exact hα x
  have dα := ratFun_differentiableOn hq N α ρ hbα
  have dβ := ratFun_differentiableOn hq N β ρ hbβ

  have near : ∀ (γ : Fin N → ℂˣ) (φ : GL (Fin N) k → ℂ), IsBorelSph k (borelParam (resCard k) γ) φ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε →
        HasSum (fun e => ((wR e : ℂ) * zonalInt μK φ (torusElt k (Fin N) ϖ e)) * z ^ n e)
          (ratFun (resCard k) N γ z) := by
    intro γ φ hφ
    obtain ⟨s₀, h⟩ := hZ γ φ hφ
    refine ⟨(resCard k : ℝ) ^ (-s₀), Real.rpow_pos_of_pos hq0 _, fun z hz hzε => ?_⟩
    obtain ⟨s', hs', rfl⟩ := exists_cpow_neg_eq hq s₀ (norm_pos_iff.1 hz) hzε
    have := h s' hs'
    rw [ratFun_cpow hq N γ s'] at this
    exact (funext fun e => hterm e s' _) ▸ this
  obtain ⟨εα, hεα, hnα⟩ := near α ψ hψ
  obtain ⟨εβ, hεβ, hnβ⟩ := near β ψ' hψ'
  have hsum := GlobalTheory.summable_nonneg_family_of_differentiableOn c n (ratFun (resCard k) N β) _ εβ hc0 hεβ dβ fun z h1 h2 => by
    have := hnβ z h1 h2
    simpa only [hcb] using this
  have hid := GlobalTheory.hasSum_of_dominated_of_eq_near_zero' b c n (ratFun (resCard k) N α) _ εα hbc hsum hεα dα hnα
  have hz : ‖(resCard k : ℂ) ^ (-s)‖ = (resCard k : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have hzr : ‖(resCard k : ℂ) ^ (-s)‖ < (resCard k : ℝ) ^ (1 / 2 - ρ) := by
    rw [hz, Real.rpow_lt_rpow_left_iff hq1]
    linarith
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => ?_) (hsum _ (norm_nonneg _) hzr)
    rw [hterm, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc e) (pow_nonneg (norm_nonneg _) _)
  · have := hid _ hzr
    rw [← ratFun_cpow hq N α s] at this
    exact (funext fun e => hterm e s _) ▸ this

end GlobalTheory.DoublingSeries
