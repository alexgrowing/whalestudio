import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LocNorm
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite

open QuadraticAlgebra NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

private theorem sq_of_norm {K R : Type} [Field K] [Field R] (f : K →+* R) {Δ τ : K} (a : R) (ha : a ^ 2 = f τ * a - 1)
    (d : EL Δ τ) (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : ∃ x y : R, x ^ 2 - f Δ * y ^ 2 = a := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := d
  have h1 : p0 ^ 2 - Δ * q0 ^ 2 - (p1 ^ 2 - Δ * q1 ^ 2) = 0 := by
    have := congrArg (fun z : EL Δ τ => z.re.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have h2 : 2 * (p0 * p1 - Δ * q0 * q1) + τ * (p1 ^ 2 - Δ * q1 ^ 2) = 1 := by
    have := congrArg (fun z : EL Δ τ => z.im.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have g1 := congrArg f h1
  have g2 := congrArg f h2
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, map_one, map_ofNat] at g1 g2
  exact ⟨f p0 + f p1 * a, f q0 + f q1 * a, by linear_combination g1 + a * g2 + (f p1 ^ 2 - f Δ * f q1 ^ 2) * ha⟩

private theorem norm_of_sq {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ)
    (h : x ^ 2 - algebraMap K (Etau K τ) Δ * y ^ 2 = ω) : ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ) := by
  obtain ⟨p0, p1⟩ := x
  obtain ⟨q0, q1⟩ := y
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  refine ⟨⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩, ?_⟩
  ext <;> simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination h1
  · ring
  · linear_combination h2
  · ring

private theorem hasse {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (hΔ : Δ ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (a : E) (ha : a ^ 2 = algebraMap F E τ * a - 1) :
    ∃ x y : E, x ^ 2 - algebraMap F E Δ * y ^ 2 = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have key : hs (algebraMap F E Δ) a = 1 := by
    refine hsHasse E _ a ((map_ne_zero _).2 hΔ) ha0 (fun σ => ?_) fun w => ?_
    · exfalso
      have h1 := hτ (σ.comp (algebraMap F E))
      have h2 := congrArg σ ha
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, RingHom.comp_apply] at h1 h2
      nlinarith [sq_nonneg (2 * σ a - σ (algebraMap F E τ))]
    · let v : Pl F := w.under (𝓞 F)
      haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
      have hf : ∀ x : F, KStar.Choice.complMap v w (cv v x) = cv w (algebraMap F E x) :=
        KStar.Choice.complMap_algebraMap v w
      unfold hs
      rw [if_pos]
      by_cases hv : v ∈ D.Sg
      · obtain ⟨s, hs⟩ := h.split v hv
        have e := congrArg (KStar.Choice.complMap v w) hs
        rw [hf, map_mul] at e
        set r := KStar.Choice.complMap v w s
        have hr : r ≠ 0 := by
          rintro h0
          rw [h0, mul_zero, map_eq_zero, map_eq_zero] at e
          exact hΔ e
        haveI : CharZero (Kv w) := algebraRat.charZero _
        refine ⟨(cv w a + 1) / 2, (cv w a - 1) / (2 * r), ?_⟩
        rw [e]
        field_simp
        ring
      · obtain ⟨d, hd⟩ := locNorm (Ov v) (Kv v) (cv v Δ) (cv v τ) (h.off v hv) (hi v hv)
        rw [← hf]
        refine sq_of_norm _ _ ?_ d hd
        rw [hf, ← map_pow, ha, map_sub, map_mul, map_one]
  unfold hs at key
  by_contra hn
  rw [if_neg hn] at key
  norm_num at key

private theorem d_ex {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (σ : F →+* ℝ) :
    ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau F τ) := by
  have hΔ : Δ ≠ 0 := fun h0 => by simpa [h0] using h.neg σ
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r hr => by
    have h1 := hτ σ
    have h2 := congrArg σ hr
    simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_one, map_ofNat] at h1 h2
    nlinarith [sq_nonneg (2 * σ r - σ τ)]⟩
  haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _
  obtain ⟨x, y, hxy⟩ := hasse D h τ hτ hi hΔ (Etau F τ) ω (by ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
  exact norm_of_sq x y hxy

private theorem tr_re {K : Type} [Field K] {Δ τ : K} (y : EL Δ τ) :
    (QuadraticAlgebra.trace (y * star (sigL y))).re =
      2 * (y.re.re ^ 2 + τ * y.re.re * y.im.re + y.im.re ^ 2) - 2 * Δ * (y.re.im ^ 2 + τ * y.re.im * y.im.im + y.im.im ^ 2) := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := y
  simp [sigL, QuadraticAlgebra.trace_def, two_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem q_nonneg {t : ℝ} (ht : t ^ 2 - 4 < 0) (p q : ℝ) : 0 ≤ p ^ 2 + t * p * q + q ^ 2 := by
  nlinarith [sq_nonneg (2 * p + t * q), mul_nonneg (sub_nonneg.2 (show t ^ 2 ≤ 4 by linarith)) (sq_nonneg q)]

private theorem q_zero {t : ℝ} (ht : t ^ 2 - 4 < 0) {p q : ℝ} (h : p ^ 2 + t * p * q + q ^ 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    nlinarith [sq_nonneg (2 * p + t * q), mul_pos (sub_pos.2 (show t ^ 2 < 4 by linarith)) (sq_pos_of_ne_zero hq)]
  subst hq
  exact ⟨by simpa using h, rfl⟩

private theorem tr_pos {K : Type} [Field K] {Δ τ : K} (σ : K →+* ℝ) (hΔ : σ Δ < 0) (hτ : σ (τ ^ 2 - 4) < 0) (y : EL Δ τ) :
    0 ≤ σ (QuadraticAlgebra.trace (y * star (sigL y))).re ∧ (y ≠ 0 → 0 < σ (QuadraticAlgebra.trace (y * star (sigL y))).re) := by
  rw [tr_re]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hτ ⊢
  have h1 := q_nonneg hτ (σ y.re.re) (σ y.im.re)
  have h2 := q_nonneg hτ (σ y.re.im) (σ y.im.im)
  have h3 := mul_nonneg (neg_pos.2 hΔ).le h2
  refine ⟨by linarith, fun hy => ?_⟩
  by_contra hn
  have e1 := q_zero hτ (le_antisymm (by linarith) h1)
  have e2 := q_zero hτ ((mul_eq_zero.1 (le_antisymm (by linarith) h3)).resolve_left (neg_pos.2 hΔ).ne')
  simp only [map_eq_zero] at e1 e2
  exact hy (by ext <;> simp [e1.1, e1.2, e2.1, e2.2])

private theorem sig_mul {K : Type} [Field K] {Δ τ : K} (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sig_sig {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sig_star {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sig_one_add {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (1 + x) = 1 + sigL x := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem posF {F : Type} [Field F] {Δ τ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hτ : IsCM τ) (d : EL Δ τ) :
    PosF 1 (1 + sigL d * star d) := by
  rintro ⟨⟨p, q⟩, x⟩ hx σ
  have e : (1 + sigL d * star d) * x * star (sigL x) = x * star (sigL x) + (sigL d * x) * star (sigL (sigL d * x)) := by
    rw [sig_mul, sig_sig, star_mul]
    ring
  have e2 : (herm 1 (1 + sigL d * star d) (⟨p, q⟩, x) (⟨p, q⟩, x)).re = p ^ 2 - Δ * q ^ 2 +
      ((QuadraticAlgebra.trace (x * star (sigL x))).re + (QuadraticAlgebra.trace ((sigL d * x) * star (sigL (sigL d * x)))).re) := by
    simp only [herm]
    rw [e, map_add, map_one, one_mul]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  rw [e2]
  have h1 := tr_pos σ (hΔ σ) (hτ σ) x
  have h2 := (tr_pos σ (hΔ σ) (hτ σ) (sigL d * x)).1
  simp only [map_add σ, map_sub σ, map_mul σ, map_pow σ]
  have h3 := mul_nonneg (neg_pos.2 (hΔ σ)).le (sq_nonneg (σ q))
  have h4 := sq_nonneg (σ p)
  by_cases h0 : x = 0
  · by_contra hn
    have hp : σ p ^ 2 = 0 := le_antisymm (by linarith [h1.1]) h4
    have hq : σ q ^ 2 = 0 := (mul_eq_zero.1 (le_antisymm (by linarith [h1.1]) h3)).resolve_left (neg_pos.2 (hΔ σ)).ne'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, map_eq_zero] at hp hq
    exact hx (by rw [hp, hq, h0]; rfl)
  · linarith [h1.2 h0]

end UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

open UpperTheory.V.Z.Sym.Glob.GlobalDataExistence in
theorem UpperTheory.V.Z.Sym.Glob.datEx :
    UpperTheory.V.Z.Sym.Glob.DatEx := by
  intro F _ _ Δ D h τ hτ hi
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  obtain ⟨d, hd⟩ := d_ex D h τ hτ hi σ
  have hp := posF h.neg hτ d
  refine ⟨d, _, ⟨fun h0 => by simpa [h0] using hτ σ, one_ne_zero, hd, ?_, ?_, ?_⟩, hp⟩
  · haveI : Module.Finite F (EL Δ τ) := Module.Finite.trans (Lsq F Δ) _
    haveI : IsArtinianRing (EL Δ τ) := IsArtinianRing.of_finite F _
    refine IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun x hx => ?_)
    by_contra h0
    have := hp (0, x) (fun e => h0 (congrArg Prod.snd e)) σ
    simp [herm, hx] at this
  · rw [sig_one_add, sig_mul, sig_sig, sig_star, star_add, star_one, star_mul, star_star]
  · have e : (d * sigL d) * star (d * sigL d) = 1 := by
      rw [hd]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    rw [star_mul] at e
    rw [sig_one_add, sig_mul, sig_sig, sig_star]
    linear_combination -e
