import Mathlib

open MeasureTheory Polynomial
open scoped ENNReal

namespace PositivityTheory.Rg.Tf.Loc

noncomputable section

section Abstract

variable {G : Type*} [Group G]

def twConj (θ : Monoid.End G) (g δ : G) : G := g⁻¹ * δ * θ g

def TwConjugate (θ : Monoid.End G) (δ δ' : G) : Prop := ∃ g : G, δ' = twConj θ g δ

def twNorm (θ : Monoid.End G) (m : ℕ) (δ : G) : G :=
  ((List.range m).map fun i => (θ ^ i) δ).prod

@[simp] theorem twNorm_zero (θ : Monoid.End G) (δ : G) : twNorm θ 0 δ = 1 := by
  simp [twNorm]

theorem twNorm_succ (θ : Monoid.End G) (m : ℕ) (δ : G) :
    twNorm θ (m + 1) δ = twNorm θ m δ * (θ ^ m) δ := by
  simp [twNorm, List.range_succ, List.prod_append]

theorem pow_succ_apply (θ : Monoid.End G) (m : ℕ) (g : G) :
    (θ ^ (m + 1)) g = (θ ^ m) (θ g) := by
  rw [pow_succ]; rfl

theorem pow_succ_apply' (θ : Monoid.End G) (m : ℕ) (g : G) :
    (θ ^ (m + 1)) g = θ ((θ ^ m) g) := by
  rw [pow_succ']; rfl

theorem twNorm_twConj (θ : Monoid.End G) (m : ℕ) (g δ : G) :
    twNorm θ m (twConj θ g δ) = g⁻¹ * twNorm θ m δ * (θ ^ m) g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, ih, twConj, map_mul, map_mul, map_inv, pow_succ_apply θ m g]
    group

theorem twNorm_twConj_of_pow_eq_one (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (g δ : G) :
    twNorm θ ℓ (twConj θ g δ) = g⁻¹ * twNorm θ ℓ δ * g := by
  rw [twNorm_twConj, hℓ]; rfl

theorem map_twNorm (θ : Monoid.End G) (m : ℕ) (δ : G) :
    θ (twNorm θ m δ) = δ⁻¹ * twNorm θ m δ * (θ ^ m) δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, map_mul, ih, ← pow_succ_apply']
    group

theorem map_twNorm_of_pow_eq_one (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) :
    θ (twNorm θ ℓ δ) = δ⁻¹ * twNorm θ ℓ δ * δ := by
  rw [map_twNorm, hℓ]; rfl

def twCent (θ : Monoid.End G) (δ : G) : Subgroup G where
  carrier := {g | twConj θ g δ = δ}
  one_mem' := by simp [twConj]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, twConj] at *
    rw [map_mul, show (a * b)⁻¹ * δ * (θ a * θ b) = b⁻¹ * (a⁻¹ * δ * θ a) * θ b by group, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, twConj] at *
    calc a⁻¹⁻¹ * δ * θ a⁻¹ = a * (a⁻¹ * δ * θ a) * (θ a)⁻¹ := by rw [ha, map_inv, inv_inv]
      _ = δ := by group

theorem mem_twCent (θ : Monoid.End G) (δ g : G) : g ∈ twCent θ δ ↔ g⁻¹ * δ * θ g = δ := Iff.rfl

theorem twConj_mul_left (θ : Monoid.End G) (δ : G) {h : G} (hh : h ∈ twCent θ δ) (g : G) :
    twConj θ (h * g) δ = twConj θ g δ := by
  have hh' : h⁻¹ * δ * θ h = δ := hh
  simp only [twConj, map_mul]
  rw [show (h * g)⁻¹ * δ * (θ h * θ g) = g⁻¹ * (h⁻¹ * δ * θ h) * θ g by group, hh']

theorem twCent_commute_twNorm (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) {g : G}
    (hg : g ∈ twCent θ δ) : g * twNorm θ ℓ δ = twNorm θ ℓ δ * g := by
  have h1 := twNorm_twConj_of_pow_eq_one θ hℓ g δ
  have hg' : twConj θ g δ = δ := hg
  rw [hg'] at h1
  calc g * twNorm θ ℓ δ = g * (g⁻¹ * twNorm θ ℓ δ * g) := by rw [← h1]
    _ = twNorm θ ℓ δ * g := by group

theorem conj_commute_of_commute {x h c : G} (hx : x * (h * c * h⁻¹) = (h * c * h⁻¹) * x) :
    (h⁻¹ * x * h) * c = c * (h⁻¹ * x * h) := by
  calc (h⁻¹ * x * h) * c = h⁻¹ * (x * (h * c * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * c * h⁻¹) * x) * h := by rw [hx]
    _ = c * (h⁻¹ * x * h) := by group

theorem conj_twCent_mem_centralizer (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) {δ h c : G}
    (hN : twNorm θ ℓ δ = h * c * h⁻¹) {x : G} (hx : x ∈ twCent θ δ) :
    h⁻¹ * x * h ∈ Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := twCent_commute_twNorm θ hℓ δ hx
  rw [hN] at this
  exact conj_commute_of_commute this

variable [MeasurableSpace G]

def IsQuotNormaliser (H : Subgroup G) (μH : Measure H) (ρ : G → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ g : G, ∫⁻ h, ρ ((h : G) * g) ∂μH = 1

open Classical in

def quotLIntegral (μG : Measure G) (H : Subgroup G) (μH : Measure H) (F : G → ℝ≥0∞) : ℝ≥0∞ :=
  if hρ : ∃ ρ, IsQuotNormaliser H μH ρ then ∫⁻ g, F g * hρ.choose g ∂μG else 0

theorem lintegral_normaliser_eq [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫⁻ g, F g * ρ g ∂μG = ∫⁻ g, F g * ρ' g ∂μG := by
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd

  have e1 : ∫⁻ g, F g * ρ g ∂μG = ∫⁻ h, ∫⁻ g, F g * ρ g * ρ' ((h : G) * g) ∂μG ∂μH := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul, hρ'.2 g, mul_one]
      exact hρ'.1.comp (measurable_subtype_coe.mul_const g)
    · exact ((hF.comp measurable_snd).mul (hρ.1.comp measurable_snd)).mul
        (hρ'.1.comp hmulH) |>.aemeasurable

  have e2 : ∀ h : H, ∫⁻ g, F g * ρ g * ρ' ((h : G) * g) ∂μG =
      ∫⁻ g, F g * ρ' g * ρ (((h⁻¹ : H) : G) * g) ∂μG := by
    intro h
    rw [← lintegral_mul_left_eq_self _ ((h : G)⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [hFH _ (H.inv_mem h.2), mul_inv_cancel_left, Subgroup.coe_inv]
    ring

  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun h : H => ρ ((h : G) * g)), hρ.2 g, mul_one]
    exact hρ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const g)
  · have : Measurable fun p : G × H => ((p.2⁻¹ : H) : G) * p.1 :=
      (measurable_subtype_coe.comp (measurable_snd.inv)).mul measurable_fst
    exact ((hF.comp measurable_fst).mul (hρ'.1.comp measurable_fst)).mul
      (hρ.1.comp this) |>.aemeasurable

theorem quotLIntegral_eq [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotLIntegral μG H μH F = ∫⁻ g, F g * ρ g ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotLIntegral, dif_pos hex]
  exact lintegral_normaliser_eq hF hFH hex.choose_spec hρ

def twOrbIntegral (θ : Monoid.End G) (μG : Measure G) (δ : G) (μδ : Measure (twCent θ δ))
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  quotLIntegral μG (twCent θ δ) μδ (fun g => f (twConj θ g δ))

def orbIntegral (μG : Measure G) (γ : G) (μγ : Measure (Subgroup.centralizer {γ}))
    (f : G → ℝ≥0∞) : ℝ≥0∞ :=
  quotLIntegral μG (Subgroup.centralizer {γ}) μγ (fun g => f (g⁻¹ * γ * g))

end Abstract

section Galois

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

def sigmaGL (τ : E ≃ₐ[k] E) : Monoid.End (GL n E) :=
  Matrix.GeneralLinearGroup.map (τ.toAlgHom.toRingHom)

theorem sigmaGL_val (τ : E ≃ₐ[k] E) (g : GL n E) :
    ((sigmaGL τ g : GL n E) : Matrix n n E) = (g : Matrix n n E).map τ := rfl

theorem sigmaGL_mul (τ τ' : E ≃ₐ[k] E) :
    (sigmaGL (τ * τ') : Monoid.End (GL n E)) = sigmaGL τ * sigmaGL τ' := by
  ext g i j
  rfl

theorem sigmaGL_one : (sigmaGL (1 : E ≃ₐ[k] E) : Monoid.End (GL n E)) = 1 := by
  ext g i j
  rfl

theorem sigmaGL_pow (τ : E ≃ₐ[k] E) (m : ℕ) :
    (sigmaGL (τ ^ m) : Monoid.End (GL n E)) = sigmaGL τ ^ m := by
  induction m with
  | zero => simpa using sigmaGL_one
  | succ m ih => rw [pow_succ, sigmaGL_mul, ih, pow_succ]

def incl : GL n k →* GL n E := Matrix.GeneralLinearGroup.map (algebraMap k E)

def normGL (σ : E ≃ₐ[k] E) (δ : GL n E) : GL n E :=
  twNorm (sigmaGL σ) (Module.finrank k E) δ

theorem charpoly_twNorm_map (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (δ : GL n E) :
    ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly.map (σ.toAlgHom.toRingHom) =
      ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly := by
  have hθ : (sigmaGL σ : Monoid.End (GL n E)) ^ ℓ = 1 := by rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  rw [← Matrix.charpoly_map]
  have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ
  have h2 : ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).map σ.toAlgHom.toRingHom =
      ((sigmaGL σ (twNorm (sigmaGL σ) ℓ δ) : GL n E) : Matrix n n E) := rfl
  rw [h2, h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

theorem coeff_charpoly_normGL_fixed (σ : E ≃ₐ[k] E) (hℓ : σ ^ Module.finrank k E = 1)
    (δ : GL n E) (i : ℕ) :
    σ (((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i) =
      ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i := by
  have h := congrArg (fun p => Polynomial.coeff p i) (charpoly_twNorm_map σ hℓ δ)
  simpa [normGL, Polynomial.coeff_map] using h

theorem charpoly_normGL_lifts [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (δ : GL n E) :
    ∃ P : k[X], P.map (algebraMap k E) = ((normGL σ δ : GL n E) : Matrix n n E).charpoly := by
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hfix : ∀ i, ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i ∈
      Set.range (algebraMap k E) := by
    intro i
    set x := ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact coeff_charpoly_normGL_fixed σ hℓ δ i
    have hall : ∀ τ : E ≃ₐ[k] E, τ x = x := by
      intro τ
      have := (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have := (IsGalois.mem_bot_iff_fixed x).mpr hall
    rwa [IntermediateField.mem_bot] at this
  exact (Polynomial.lifts_iff_coeff_lifts _).mpr hfix

def IsTwRegSemisimple (σ : E ≃ₐ[k] E) (δ : GL n E) : Prop :=
  ((normGL σ δ : GL n E) : Matrix n n E).charpoly.Separable

def IsRegSemisimple (γ : GL n k) : Prop := ((γ : GL n k) : Matrix n n k).charpoly.Separable

def IsNormOf (σ : E ≃ₐ[k] E) (δ : GL n E) (γ : GL n k) : Prop :=
  ∃ h : GL n E, normGL σ δ = h * incl γ * h⁻¹

end Galois

section Units

variable {n : Type*} [Fintype n] [DecidableEq n]

def unitGL (F : Type*) [Field F] [ValuativeRel F] : Subgroup (GL n F) :=
  (Matrix.GeneralLinearGroup.map (Valuation.integer (ValuativeRel.valuation F)).subtype).range

def unitFn (F : Type*) [Field F] [ValuativeRel F] : GL n F → ℝ≥0∞ :=
  Set.indicator ((unitGL (n := n) F : Subgroup (GL n F)) : Set (GL n F)) 1

end Units

def IsUnramifiedLoc (k E : Type*) [Field k] [Field E] [Algebra k E] [ValuativeRel E] : Prop :=
  ∃ π : k, ValuativeRel.valuation E (algebraMap k E π) < 1 ∧
    ∀ x : E, ValuativeRel.valuation E x < 1 →
      ValuativeRel.valuation E x ≤ ValuativeRel.valuation E (algebraMap k E π)

def BCFLUnit : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)),
      μE.IsHaarMeasure → μk.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1 →
      (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
          (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
          IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ →
          μδ.IsHaarMeasure → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
            Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
          twOrbIntegral (sigmaGL σ) μE δ μδ (unitFn E) = orbIntegral μk γ μγ (unitFn k)) ∧
      (∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) →
          μγ.IsHaarMeasure → orbIntegral μk γ μγ (unitFn k) = 0)

section Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

def invTransposeGL : Monoid.End (GL n E) where
  toFun g := ⟨Matrix.transpose ((g⁻¹ : GL n E) : Matrix n n E), Matrix.transpose (g : Matrix n n E),
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by
    show Matrix.transpose (((1 : GL n E)⁻¹ : GL n E) : Matrix n n E) = 1
    simp)
  map_mul' := fun a b => Units.ext (by
    show Matrix.transpose (((a * b)⁻¹ : GL n E) : Matrix n n E) =
      Matrix.transpose ((a⁻¹ : GL n E) : Matrix n n E) * Matrix.transpose ((b⁻¹ : GL n E) : Matrix n n E)
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

def thetaGL (σ : E ≃ₐ[k] E) (J : GL n E) : Monoid.End (GL n E) :=
  (MulAut.conj J).toMonoidHom.comp (invTransposeGL.comp (sigmaGL σ))

theorem thetaGL_apply (σ : E ≃ₐ[k] E) (J g : GL n E) :
    thetaGL σ J g = J * invTransposeGL (sigmaGL σ g) * J⁻¹ := rfl

def unitaryGL (σ : E ≃ₐ[k] E) (J : GL n E) : Subgroup (GL n E) :=
  MonoidHom.eqLocus (thetaGL σ J) (MonoidHom.id _)

def normU (σ : E ≃ₐ[k] E) (J δ : GL n E) : GL n E := twNorm (thetaGL σ J) 2 δ

def unitFnU [ValuativeRel E] (σ : E ≃ₐ[k] E) (J : GL n E) : unitaryGL σ J → ℝ≥0∞ :=
  Set.indicator {u | (u : GL n E) ∈ unitGL (n := n) E} 1

variable [TopologicalSpace E] [MeasurableSpace (GL n E)]

structure StableData (σ : E ≃ₐ[k] E) (J : GL n E) (γ : unitaryGL σ J)
    (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))) where
  reps : Finset (unitaryGL σ J)
  conj : unitaryGL σ J → GL n E
  meas : (γ' : unitaryGL σ J) → Measure (Subgroup.centralizer ({γ'} : Set (unitaryGL σ J)))
  conj_spec : ∀ γ' ∈ reps, ((γ' : GL n E)) = (conj γ')⁻¹ * (γ : GL n E) * conj γ'
  distinct : ∀ γ₁ ∈ reps, ∀ γ₂ ∈ reps, (∃ u : unitaryGL σ J, γ₂ = u⁻¹ * γ₁ * u) → γ₁ = γ₂
  exhaust : ∀ γ'' : unitaryGL σ J, (∃ g : GL n E, (γ'' : GL n E) = g⁻¹ * (γ : GL n E) * g) →
    ∃ γ' ∈ reps, ∃ u : unitaryGL σ J, γ'' = u⁻¹ * γ' * u
  haar : ∀ γ' ∈ reps, (meas γ').IsHaarMeasure
  compat : ∀ γ' ∈ reps,
    Measure.map (fun t : Subgroup.centralizer ({γ'} : Set (unitaryGL σ J)) =>
        conj γ' * ((t : unitaryGL σ J) : GL n E) * (conj γ')⁻¹) (meas γ') =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ J)) =>
        ((t : unitaryGL σ J) : GL n E)) μγ

def stableOrbIntegralU (σ : E ≃ₐ[k] E) (J : GL n E) (μU : Measure (unitaryGL σ J))
    {γ : unitaryGL σ J} {μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))}
    (D : StableData σ J γ μγ) (f : unitaryGL σ J → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ γ' ∈ D.reps, orbIntegral μU γ' (D.meas γ') f

structure TwStableData (σ : E ≃ₐ[k] E) (J : GL n E) (γ : unitaryGL σ J)
    (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))) where
  reps : Finset (GL n E)
  conj : GL n E → GL n E
  meas : (δ : GL n E) → Measure (twCent (thetaGL σ J) δ)
  norm_spec : ∀ δ ∈ reps, normU σ J δ = conj δ * (γ : GL n E) * (conj δ)⁻¹
  distinct : ∀ δ₁ ∈ reps, ∀ δ₂ ∈ reps, TwConjugate (thetaGL σ J) δ₁ δ₂ → δ₁ = δ₂
  exhaust : ∀ δ : GL n E, (∃ g : GL n E, normU σ J δ = g * (γ : GL n E) * g⁻¹) →
    ∃ δ' ∈ reps, TwConjugate (thetaGL σ J) δ' δ
  haar : ∀ δ ∈ reps, (meas δ).IsHaarMeasure
  compat : ∀ δ ∈ reps,
    Measure.map (fun x : twCent (thetaGL σ J) δ => (conj δ)⁻¹ * (x : GL n E) * conj δ) (meas δ) =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ J)) =>
        ((t : unitaryGL σ J) : GL n E)) μγ

def twStableOrbIntegralU (σ : E ≃ₐ[k] E) (J : GL n E) (μE : Measure (GL n E))
    {γ : unitaryGL σ J} {μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J)))}
    (T : TwStableData σ J γ μγ) (f : GL n E → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ δ ∈ T.reps, twOrbIntegral (thetaGL σ J) μE δ (T.meas δ) f

end Unitary

def BCFLUnitU : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (n : ℕ) (J : GL (Fin n) E), J ∈ unitGL (n := Fin n) E → thetaGL σ J ^ 2 = 1 →
    ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ J)),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      ∀ (γ : unitaryGL σ J) (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ J))))
        (D : StableData σ J γ μγ) (T : TwStableData σ J γ μγ),
        (((γ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
        μγ.IsHaarMeasure →
        twStableOrbIntegralU σ J μE T (unitFn E) = stableOrbIntegralU σ J μU D (unitFnU σ J)

section ComplexValued

variable {G : Type*} [Group G] [MeasurableSpace G]

open Classical in

def quotIntegral (μG : Measure G) (H : Subgroup G) (μH : Measure H) (F : G → ℂ) : ℂ :=
  if hρ : ∃ ρ, IsQuotNormaliser H μH ρ then ∫ g, F g * ((hρ.choose g).toReal : ℂ) ∂μG else 0

def twOrbIntegralC (θ : Monoid.End G) (μG : Measure G) (δ : G) (μδ : Measure (twCent θ δ))
    (f : G → ℂ) : ℂ :=
  quotIntegral μG (twCent θ δ) μδ (fun g => f (twConj θ g δ))

def orbIntegralC (μG : Measure G) (γ : G) (μγ : Measure (Subgroup.centralizer {γ}))
    (f : G → ℂ) : ℂ :=
  quotIntegral μG (Subgroup.centralizer {γ}) μγ (fun g => f (g⁻¹ * γ * g))

end ComplexValued

section Iwahori

variable {m : ℕ}

def IsUniformiser {F : Type*} [Field F] [ValuativeRel F] (ϖ : F) : Prop :=
  ValuativeRel.valuation F ϖ < 1 ∧ ϖ ≠ 0 ∧
    ∀ x : F, ValuativeRel.valuation F x < 1 → ValuativeRel.valuation F x ≤ ValuativeRel.valuation F ϖ

def iwahori (F : Type*) [Field F] [ValuativeRel F] : Set (GL (Fin m) F) :=
  {g | g ∈ unitGL (n := Fin m) F ∧
    ∀ i j : Fin m, j < i → ValuativeRel.valuation F ((g : Matrix (Fin m) (Fin m) F) i j) < 1}

def diagPow {F : Type*} [Field F] (ϖ : Fˣ) (a : Fin m → ℤ) : GL (Fin m) F :=
  ⟨Matrix.diagonal fun i => ((ϖ ^ a i : Fˣ) : F), Matrix.diagonal fun i => (((ϖ ^ a i)⁻¹ : Fˣ) : F),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩

def StrictlyDominant (a : Fin m → ℤ) : Prop := StrictAnti a

def iwahoriFn (F : Type*) [Field F] [ValuativeRel F] (x : GL (Fin m) F) : GL (Fin m) F → ℂ :=
  Set.indicator {g | ∃ a ∈ iwahori (m := m) F, ∃ b ∈ iwahori (m := m) F, g = a * x * b} 1

end Iwahori

section UnitaryKappa

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

def theta1 (σ : E ≃ₐ[k] E) : Monoid.End (GL n E) := thetaGL σ 1

theorem sigmaGL_invTransposeGL (τ : E ≃ₐ[k] E) (g : GL n E) :
    sigmaGL τ (invTransposeGL g) = invTransposeGL (sigmaGL τ g) := by
  apply Units.ext
  show (Matrix.transpose ((g⁻¹ : GL n E) : Matrix n n E)).map τ.toAlgHom.toRingHom =
    Matrix.transpose (((sigmaGL τ g)⁻¹ : GL n E) : Matrix n n E)
  rw [← map_inv]
  rfl

theorem invTransposeGL_invTransposeGL (g : GL n E) :
    invTransposeGL (invTransposeGL g) = g :=
  Units.ext (Matrix.transpose_transpose _)

theorem theta1_sq (σ : E ≃ₐ[k] E) (hσ : σ ^ 2 = 1) :
    (theta1 σ : Monoid.End (GL n E)) ^ 2 = 1 := by
  have hθ : ∀ g : GL n E, theta1 σ g = invTransposeGL (sigmaGL σ g) := fun g => by
    rw [theta1, thetaGL_apply, one_mul, inv_one, mul_one]
  have h2 : (sigmaGL σ : Monoid.End (GL n E)) ^ 2 = 1 := by
    rw [← sigmaGL_pow, hσ, sigmaGL_one]
  have hσσ : ∀ g : GL n E, sigmaGL σ (sigmaGL σ g) = g := fun g => by
    show (sigmaGL σ * sigmaGL σ : Monoid.End (GL n E)) g = g
    rw [← pow_two, h2]
    rfl
  refine MonoidHom.ext fun g => ?_
  rw [pow_two]
  show theta1 σ (theta1 σ g) = g
  rw [hθ, hθ, sigmaGL_invTransposeGL, invTransposeGL_invTransposeGL, hσσ]

def unitFnC (F : Type*) [Field F] [ValuativeRel F] : GL n F → ℂ :=
  Set.indicator ((unitGL (n := n) F : Subgroup (GL n F)) : Set (GL n F)) 1

def unitFnUC [ValuativeRel E] (σ : E ≃ₐ[k] E) (J : GL n E) : unitaryGL σ J → ℂ :=
  Set.indicator {u | (u : GL n E) ∈ unitGL (n := n) E} 1

variable [TopologicalSpace E] [MeasurableSpace (GL n E)]

structure KappaData (σ : E ≃ₐ[k] E) (γ₀ : GL n E) (ν : Measure (GL n E)) where
  forms : Finset (GL n E)
  herm : ∀ J ∈ forms, thetaGL σ J ^ 2 = 1
  ι : Type
  fin : Fintype ι
  form : ι → GL n E
  form_mem : ∀ x, form x ∈ forms
  rep : (x : ι) → unitaryGL σ (form x)
  conj : ι → GL n E
  meas : (x : ι) → Measure (Subgroup.centralizer ({rep x} : Set (unitaryGL σ (form x))))
  sign : ι → ℤ
  conj_spec : ∀ x, ((rep x : unitaryGL σ (form x)) : GL n E) = (conj x)⁻¹ * γ₀ * conj x
  distinct : ∀ x y, form x = form y →
    (∃ u ∈ unitaryGL σ (form x), ((rep y : unitaryGL σ (form y)) : GL n E) =
      u⁻¹ * ((rep x : unitaryGL σ (form x)) : GL n E) * u) → x = y
  exhaust : ∀ J ∈ forms, ∀ γ'' ∈ unitaryGL σ J, (∃ g : GL n E, γ'' = g⁻¹ * γ₀ * g) →
    ∃ x, form x = J ∧ ∃ u ∈ unitaryGL σ J,
      γ'' = u⁻¹ * ((rep x : unitaryGL σ (form x)) : GL n E) * u
  sign_spec : ∀ x, sign x = 1 ∨ sign x = -1
  haar : ∀ x, (meas x).IsHaarMeasure
  compat : ∀ x,
    Measure.map (fun t : Subgroup.centralizer ({rep x} : Set (unitaryGL σ (form x))) =>
      conj x * ((t : unitaryGL σ (form x)) : GL n E) * (conj x)⁻¹) (meas x) = ν

def kappaOrbIntegral (σ : E ≃ₐ[k] E) {γ₀ : GL n E} {ν : Measure (GL n E)}
    (D : KappaData σ γ₀ ν) (μU : (x : D.ι) → Measure (unitaryGL σ (D.form x)))
    (f : (x : D.ι) → unitaryGL σ (D.form x) → ℂ) : ℂ :=
  haveI := D.fin
  ∑ x, (D.sign x : ℂ) * orbIntegralC (μU x) (D.rep x) (D.meas x) (f x)

end UnitaryKappa

end

end PositivityTheory.Rg.Tf.Loc
