import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo

open NumberField Filter Topology UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob GlobalTheory.QuadSymbol

private theorem hs_sq {A : Type} [Field A] [CharZero A] {s : A} (hs0 : s ≠ 0) (x : A) : Loc.hs (s * s) x = 1 := by
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  field_simp
  ring

private theorem ev_lt {p q c : ℝ} (hp : 0 ≤ p) (h : p < q) (e : ℝ) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, e * p ^ k < c * q ^ k := by
  have hq : 0 < q := lt_of_le_of_lt hp h
  have hr0 : 0 ≤ p / q := div_nonneg hp hq.le
  have hr1 : p / q < 1 := (div_lt_one hq).mpr h
  have hlim : Tendsto (fun k : ℕ => e * (p / q) ^ k) atTop (𝓝 (e * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul e
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_lt_nhds hc)] with k hk
  have hqk : 0 < q ^ k := pow_pos hq k
  have hsplit : e * p ^ k = e * (p / q) ^ k * q ^ k := by
    rw [div_pow]
    field_simp
  rw [hsplit]
  exact mul_lt_mul_of_pos_right hk hqk

private theorem ev_sign {t d : ℝ} (ht : t ≠ 0) (h : t < 0 → 0 < d) :
    ∀ᶠ k : ℕ in atTop, 0 < t * (((t + 1) ^ k) ^ 2 - d * ((t - 1) ^ k) ^ 2) := by
  have e1 : ∀ k : ℕ, ((t + 1) ^ k) ^ 2 = ((t + 1) ^ 2) ^ k := fun k => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : ∀ k : ℕ, ((t - 1) ^ k) ^ 2 = ((t - 1) ^ 2) ^ k := fun k => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hd := h hneg
    have h1 : (t + 1) ^ 2 < (t - 1) ^ 2 := by nlinarith
    filter_upwards [ev_lt (sq_nonneg (t + 1)) h1 1 hd] with k hk
    rw [e1, e2]
    exact mul_pos_of_neg_of_neg hneg (by linarith)
  · have h1 : (t - 1) ^ 2 < (t + 1) ^ 2 := by nlinarith
    filter_upwards [ev_lt (sq_nonneg (t - 1)) h1 d one_pos] with k hk
    rw [e1, e2]
    exact mul_pos hpos (by linarith)

private theorem sign_fix {F : Type} [Field F] [NumberField F] {d t : F} (hd : ¬ IsSquare d) (ht : t ≠ 0)
    (h : ∀ σ : F →+* ℝ, σ t < 0 → 0 < σ d) :
    ∃ a b : F, a ^ 2 - d * b ^ 2 ≠ 0 ∧ ∀ σ : F →+* ℝ, 0 < σ (t * (a ^ 2 - d * b ^ 2)) := by
  haveI : Finite (F →+* ℝ) := Finite.of_injective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ)
    (fun σ τ hστ => by
      ext x
      have := congrArg (fun f : F →+* ℂ => f x) hστ
      simpa using this)
  have hev : ∀ᶠ k : ℕ in atTop, ∀ σ : F →+* ℝ,
      0 < σ t * (((σ t + 1) ^ k) ^ 2 - σ d * ((σ t - 1) ^ k) ^ 2) :=
    Filter.eventually_all.mpr fun σ => ev_sign ((map_ne_zero σ).mpr ht) (h σ)
  obtain ⟨k, hk⟩ := hev.exists
  have hne : ((t + 1) ^ k) ^ 2 - d * ((t - 1) ^ k) ^ 2 ≠ 0 := by
    intro h0
    by_cases hb : (t - 1) ^ k = 0
    · have ht1 : t = 1 := by
        have := eq_zero_of_pow_eq_zero hb
        linear_combination this
      have ha : ((t + 1) ^ k) ^ 2 = 0 := by
        rw [hb] at h0
        linear_combination h0
      have h2 : t + 1 = 0 := eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero ha)
      rw [ht1] at h2
      norm_num at h2
    · apply hd
      refine ⟨(t + 1) ^ k / (t - 1) ^ k, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
      linear_combination (-1 : F) * h0
  refine ⟨(t + 1) ^ k, (t - 1) ^ k, hne, fun σ => ?_⟩
  simpa using hk σ

private theorem hs_eta {F A : Type} [Field F] [Field A] [Algebra F A] (d : F) [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)] (x : Aˣ) :
    Loc.hs (algebraMap F A d) (x : A) = (((eta F (QuadraticAlgebra F d 0) A x : ℤˣ) : ℤ) : ℂ) := by
  unfold Loc.hs eta
  by_cases hx : x ∈ normGroup F (QuadraticAlgebra F d 0) A
  · obtain ⟨a, b, hab⟩ := (Model.mem_normGroup_sqrt d).mp hx
    rw [if_pos hx, if_pos ⟨a, b, hab.symm⟩]
    simp
  · have hn : ¬ ∃ a b : A, a ^ 2 - algebraMap F A d * b ^ 2 = (x : A) := by
      rintro ⟨a, b, hab⟩
      exact hx ((Model.mem_normGroup_sqrt d).mpr ⟨a, b, hab.symm⟩)
    rw [if_neg hx, if_neg hn]
    simp

private theorem real_sign {F : Type} [Field F] [NumberField F] (d : F) [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)] (t : Fˣ)
    (h : ∀ w : InfinitePlace F, infDiag F t w ∈ normGroup F (QuadraticAlgebra F d 0) w.Completion) (σ : F →+* ℝ)
    (ht : σ t < 0) : 0 < σ d := by
  set φ : F →+* ℂ := Complex.ofRealHom.comp σ with hφdef
  have hφ : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [φ, ComplexEmbedding.conjugate_coe_eq]
  have hw : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
  set ρ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  have key : ∀ x : F, ρ (algebraMap F (InfinitePlace.mk φ).Completion x) = σ x := by
    intro x
    have h1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
      ((WithAbs.equiv (InfinitePlace.mk φ).1).symm x)
    apply Complex.ofReal_injective
    have h2 := InfinitePlace.embedding_of_isReal_apply hw x
    rw [InfinitePlace.embedding_mk_eq_of_isReal hφ] at h2
    simp only [RingEquiv.apply_symm_apply] at h1
    have h3 : ρ (algebraMap F _ x) = InfinitePlace.embedding_of_isReal hw x := h1
    rw [h3, h2]
    rfl
  obtain ⟨a, b, hab⟩ := (Model.mem_normGroup_sqrt d).mp (h (InfinitePlace.mk φ))
  have hv : ρ ((infDiag F t (InfinitePlace.mk φ) : (InfinitePlace.mk φ).Completionˣ) :
      (InfinitePlace.mk φ).Completion) = σ t := key t
  rw [hab, map_sub, map_mul, map_pow, map_pow, key] at hv
  by_contra hd
  push_neg at hd
  nlinarith [sq_nonneg (ρ a), mul_nonneg (neg_nonneg.mpr hd) (sq_nonneg (ρ b))]

theorem UpperTheory.V.Z.Sym.Glob.symbolEx :
    UpperTheory.V.Z.Sym.Glob.SymbolEx := by
  intro F _ _ d hd0 y hfin hprod
  by_cases hsq : IsSquare d
  · obtain ⟨s, rfl⟩ := hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hd0
    refine ⟨1, one_ne_zero, fun σ => by simp, fun v => ?_⟩
    haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
    have hs' : cv v s ≠ 0 := (map_ne_zero _).mpr hs0
    rw [map_mul, hs_sq hs', hs_sq hs']
  · haveI : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) :=
      ⟨fun r hr => hsq ⟨r, by linear_combination (-1 : F) * hr⟩⟩
    haveI := Model.numberField d
    haveI := Model.isQuadratic d
    have E : ∀ (v : Pl F) (x : (Kv v)ˣ), Loc.hs (cv v d) (x : Kv v) =
        (((eta F (QuadraticAlgebra F d 0) (Kv v) x : ℤˣ) : ℤ) : ℂ) := fun v x => hs_eta d x
    obtain ⟨-, -, h3, -⟩ := exactSequence F (QuadraticAlgebra F d 0)
    have hA : AlmostNorm F (QuadraticAlgebra F d 0) y := by
      refine hfin.subset fun v hv => ?_
      simp only [Set.mem_setOf_eq] at hv ⊢
      rw [E v (y v), eta_eq_neg_one_iff.mpr hv]
      norm_num
    have hP : etaProd F (QuadraticAlgebra F d 0) y 1 = 1 := by
      unfold etaProd
      have hinf1 : ∏ w : InfinitePlace F, eta F (QuadraticAlgebra F d 0) w.Completion ((1 : InfFam F) w) = 1 :=
        Finset.prod_eq_one fun w _ => eta_eq_one_iff.mpr (one_mem _)
      rw [hinf1, mul_one]
      let g : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
      have hg : Function.Injective g := by
        intro u w huw
        have huw' : ((u : ℤ) : ℂ) = ((w : ℤ) : ℂ) := huw
        exact Units.ext (Int.cast_injective huw')
      apply hg
      rw [MonoidHom.map_finprod g (AlmostNorm.finite_mulSupport hA), map_one]
      rw [← hprod]
      apply finprod_congr
      intro v
      rw [E v (y v)]
      rfl
    obtain ⟨t, hfinN, hinfN⟩ := (h3 y 1 hA).mpr hP
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    have hreal : ∀ σ : F →+* ℝ, σ t < 0 → 0 < σ d := fun σ ht =>
      real_sign d t (fun w => by
        have hw := hinfN w
        rw [Pi.div_apply, Pi.one_apply, one_div, inv_mem_iff] at hw
        exact hw) σ ht
    obtain ⟨a, b, hab, hpos⟩ := sign_fix hsq ht0 hreal
    refine ⟨t * (a ^ 2 - d * b ^ 2), mul_ne_zero ht0 hab, hpos, fun v => ?_⟩
    have hN : algebraMap F (Kv v) (t * (a ^ 2 - d * b ^ 2)) ≠ 0 :=
      (map_ne_zero _).mpr (mul_ne_zero ht0 hab)
    obtain ⟨u, hu⟩ : ∃ u : (Kv v)ˣ, (u : Kv v) = algebraMap F (Kv v) (t * (a ^ 2 - d * b ^ 2)) :=
      ⟨Units.mk0 _ hN, rfl⟩
    have e1 : Loc.hs (cv v d) (cv v (t * (a ^ 2 - d * b ^ 2))) =
        (((eta F (QuadraticAlgebra F d 0) (Kv v) u : ℤˣ) : ℤ) : ℂ) := by
      rw [← E v u, hu]
    rw [e1, E v (y v)]
    have hyt := hfinN v
    rw [Pi.div_apply] at hyt
    have hut : u / finDiag F t v ∈ normGroup F (QuadraticAlgebra F d 0) (Kv v) := by
      rw [Model.mem_normGroup_sqrt]
      refine ⟨algebraMap F (Kv v) a, algebraMap F (Kv v) b, ?_⟩
      have hft : ((finDiag F t v : (Kv v)ˣ) : Kv v) = algebraMap F (Kv v) t := rfl
      have ht' : algebraMap F (Kv v) (t : F) ≠ 0 := (map_ne_zero _).mpr ht0
      rw [Units.val_div_eq_div_val, hft, hu, div_eq_iff ht']
      simp only [map_mul, map_sub, map_pow]
      ring
    rw [eta_eq_of_div_mem hut, eta_eq_of_div_mem hyt]
