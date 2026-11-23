import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.NstatementHypsConsistent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)

namespace GlobalTheory

namespace HyperbolicCusp

noncomputable section

def ii : E4 := IsCyclotomicExtension.zeta 4 ℚ E4

theorem ii_prim : IsPrimitiveRoot ii 4 := IsCyclotomicExtension.zeta_spec 4 ℚ E4

theorem ii_mul_ii : ii * ii = -1 := by
  have h : IsPrimitiveRoot (ii ^ 2) 2 := ii_prim.pow (by norm_num) (by norm_num : 4 = 2 * 2)
  rw [← sq]
  exact h.eq_neg_one_of_two_right

theorem ii_ne_zero : ii ≠ 0 := ii_prim.ne_zero (by norm_num)

theorem ii_isIntegral : IsIntegral ℤ ii := ii_prim.isIntegral (by norm_num)

theorem emb_ii (τ : E4 →+* ℂ) : τ ii = Complex.I ∨ τ ii = -Complex.I := by
  have h : τ ii * τ ii = Complex.I * Complex.I := by
    rw [← map_mul, ii_mul_ii, Complex.I_mul_I]; simp
  exact mul_self_eq_mul_self_iff.1 h

theorem cc_ii : cc ii = -ii := by
  obtain ⟨τ⟩ : Nonempty (E4 →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  rcases emb_ii τ with h | h <;> simp [h]

theorem exists_int_of_isIntegral {x : E4} (hx : IsIntegral ℤ x) :
    ∃ m n : ℤ, x = m + n * ii := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton ii_prim
  obtain ⟨⟨y, hy⟩, rfl⟩ := (hcl.isIntegral_iff).1 hx
  change ∃ m n : ℤ, y = m + n * ii
  clear hx
  induction hy using Algebra.adjoin_induction with
  | mem z hz => exact ⟨0, 1, by simpa using hz⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, n, rfl⟩ := ha
    obtain ⟨m', n', rfl⟩ := hb
    exact ⟨m + m', n + n', by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, n, rfl⟩ := ha
    obtain ⟨m', n', rfl⟩ := hb
    exact ⟨m * m' - n * n', m * n' + n * m', by
      push_cast; linear_combination (n * n' : E4) * ii_mul_ii⟩

theorem exists_rat (x : E4) : ∃ p q : ℚ, x = p + q * ii := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E4).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  obtain ⟨m, n, h⟩ := exists_int_of_isIntegral hki
  have hk' : (k : E4) ≠ 0 := Int.cast_ne_zero.2 hk
  refine ⟨m / k, n / k, ?_⟩
  rw [zsmul_eq_mul] at h
  push_cast
  field_simp
  linear_combination h

theorem trace_ii : Algebra.trace ℚ E4 ii = 0 := by
  have h := trace_cc ii
  rw [cc_ii, map_neg] at h
  linarith

theorem finrank_eq : Module.finrank ℚ E4 = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 E4]
  decide

theorem trace_eq (p q : ℚ) : Algebra.trace ℚ E4 (-(ii / 2) * (p + q * ii)) = q := by
  have e : -(ii / 2) * ((p : E4) + q * ii) = algebraMap ℚ E4 (q / 2) + algebraMap ℚ E4 (-(p / 2)) * ii := by
    simp only [eq_ratCast]
    push_cast
    linear_combination (-(q : E4) / 2) * ii_mul_ii
  rw [e, map_add, ← Algebra.smul_def, map_smul, trace_ii, Algebra.trace_algebraMap, finrank_eq]
  simp
  ring

theorem trace_int {t : E4} (ht : IsIntegral ℤ t) :
    ∃ k : ℤ, Algebra.trace ℚ E4 (-(ii / 2) * t) = k := by
  obtain ⟨m, n, rfl⟩ := exists_int_of_isIntegral ht
  exact ⟨n, by simpa using trace_eq m n⟩

theorem isIntegral_of_trace {t : E4}
    (h : ∀ a : E4, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E4 (-(ii / 2) * (t * a)) = k) :
    IsIntegral ℤ t := by
  obtain ⟨p, q, rfl⟩ := exists_rat t
  obtain ⟨k, hk⟩ := h 1 isIntegral_one
  obtain ⟨l, hl⟩ := h ii ii_isIntegral
  rw [mul_one, trace_eq] at hk
  have e : ((p : E4) + q * ii) * ii = ((-q : ℚ) : E4) + p * ii := by
    push_cast
    linear_combination (q : E4) * ii_mul_ii
  rw [e, trace_eq] at hl
  rw [hk, hl]
  simp only [Rat.cast_intCast]
  exact (isIntegral_intCast l).add ((isIntegral_intCast k).mul ii_isIntegral)

def gm : Matrix (Fin 2) (Fin 2) E4 := !![1, 0; 0, -1]

theorem herm_gm (x y : Fin 2 → E4) : herm gm x y = x 0 * cc (y 0) - x 1 * cc (y 1) := by
  simp [herm, gm, Fin.sum_univ_two]
  ring

theorem gm_herm (a b : Fin 2) : cc (gm a b) = gm b a := by
  fin_cases a <;> fin_cases b <;> simp [gm, cc]

theorem gm_det : gm.det ≠ 0 := by
  simp [gm, Matrix.det_fin_two]

def lat : Submodule (𝓞 E4) (Fin 2 → E4) where
  carrier := {x | ∀ a, IsIntegral ℤ (x a)}
  add_mem' hx hy a := (hx a).add (hy a)
  zero_mem' _ := isIntegral_zero
  smul_mem' c _ hx a := c.isIntegral_coe.mul (hx a)

theorem mem_lat {x : Fin 2 → E4} : x ∈ lat ↔ ∀ a, IsIntegral ℤ (x a) := Iff.rfl

theorem single_mem_lat (a : Fin 2) {c : E4} (hc : IsIntegral ℤ c) : Pi.single a c ∈ lat := by
  intro b
  by_cases h : b = a
  · subst h; simpa using hc
  · simpa [h] using isIntegral_zero

theorem lat_fg : lat.FG := by
  refine Submodule.fg_def.2 ⟨Set.range fun a : Fin 2 => (Pi.single a 1 : Fin 2 → E4),
    Set.finite_range _, le_antisymm ?_ fun x hx => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact single_mem_lat a isIntegral_one
  · rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun a => ⟨x a, hx a⟩, ?_⟩
    change ∑ a, x a • (Pi.single a 1 : Fin 2 → E4) = x
    funext b
    fin_cases b <;> simp [Fin.sum_univ_two]

theorem lat_span : Submodule.span E4 (lat : Set (Fin 2 → E4)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → E4) + x 1 • (Pi.single 1 1 : Fin 2 → E4) := by
    funext b
    fin_cases b <;> simp
  rw [hx]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_lat 0 isIntegral_one)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_lat 1 isIntegral_one)))

theorem lat_int {x y : Fin 2 → E4} (hx : x ∈ lat) (hy : y ∈ lat) : IsIntegral ℤ (herm gm x y) := by
  rw [herm_gm]
  exact ((hx 0).mul (isIntegral_cc (hy 0))).sub ((hx 1).mul (isIntegral_cc (hy 1)))

theorem lat_dual (x : Fin 2 → E4) (h : ∀ y ∈ lat, IsIntegral ℤ (herm gm x y)) : x ∈ lat := by
  have h0 := h _ (single_mem_lat 0 isIntegral_one)
  have h1 := (h _ (single_mem_lat 1 isIntegral_one)).neg
  rw [herm_gm] at h0 h1
  intro a
  fin_cases a
  · simpa [cc_one, cc_zero] using h0
  · simpa [cc_one, cc_zero] using h1

theorem traceFormDual_lat : traceFormDual (ii / 2) gm lat = lat := by
  ext x
  rw [mem_traceFormDual]
  refine ⟨fun h => lat_dual x fun y hy => isIntegral_of_trace fun a ha => ?_,
    fun hx y hy => trace_int (lat_int hx hy)⟩
  have := h (cc a • y) fun b => (isIntegral_cc ha).mul (hy b)
  have e : herm gm x (cc a • y) = herm gm x y * a := by
    simp only [herm_gm, Pi.smul_apply, smul_eq_mul, cc_mul, cc_cc]
    ring
  rwa [EFf, e] at this

def cmt : Finset (E4 →+* ℂ) := by
  classical
  exact Finset.univ.filter fun τ => τ ii = Complex.I

theorem mem_cmt {τ : E4 →+* ℂ} : τ ∈ cmt ↔ τ ii = Complex.I := by
  simp [cmt]

theorem cmt_cmType (τ : E4 →+* ℂ) : τ ∈ cmt ↔ ComplexEmbedding.conjugate τ ∉ cmt := by
  have hI : -Complex.I ≠ Complex.I := fun h => by
    have := congrArg Complex.im h
    norm_num at this
  rw [mem_cmt, mem_cmt, ComplexEmbedding.conjugate_coe_eq]
  rcases emb_ii τ with h | h <;> simp [h, hI]

theorem gram_one (τ : E4 →+* ℂ) :
    gram τ gm 1 = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, sgn, gm, Matrix.one_apply]

theorem half_ii_ne_zero : ii / 2 ≠ 0 := div_ne_zero ii_ne_zero two_ne_zero

theorem exists_flagData : ∃ X : Data E4 2, X.Ψ = cmt ∧ X.Gm = gm ∧ X.p0 = 1 ∧ X.Λ = lat ∧
    X.ξ0 = ii / 2 ∧ X.κ0 = -ii ∧ X.m = 3 ∧
    (∀ γ, γ ∈ X.Γ ↔ IsUStab gm lat γ ∧
      (∀ v ∈ lat, ∃ w ∈ lat, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) E4) v = v + 3 • w)) ∧
    ∀ la γ, X.χ la γ = 1 := by
  refine FlagData.exists_data latMinkowski E4 2 1 3 3 cmt gm lat (ii / 2) (-ii) cmt_cmType gm_herm
    gm_det (by norm_num) (fun τ _ => ⟨1, by simp, gram_one τ⟩) lat_fg lat_span le_rfl ?_
    half_ii_ne_zero (Or.inr (by ring)) (fun τ hτ => ?_) (by norm_num) fun x hx y hy => ?_
  · have h : IsCMField.complexConj E4 ii = -ii := cc_ii
    simp [cc, h, map_ofNat, neg_div]
  · simp [mem_cmt.1 hτ]
  · rw [div_self (by norm_num), one_mul]
    exact ii_isIntegral.neg.mul (lat_int hx hy)

def flagData : Data E4 2 := exists_flagData.choose

theorem flagData_Ψ : flagData.Ψ = cmt := exists_flagData.choose_spec.1
theorem flagData_Gm : flagData.Gm = gm := exists_flagData.choose_spec.2.1
theorem hyperbolicFlagData_base_point : flagData.p0 = 1 := exists_flagData.choose_spec.2.2.1
theorem flagData_Λ : flagData.Λ = lat := exists_flagData.choose_spec.2.2.2.1
theorem flagData_ξ0 : flagData.ξ0 = ii / 2 := exists_flagData.choose_spec.2.2.2.2.1
theorem flagData_κ0 : flagData.κ0 = -ii := exists_flagData.choose_spec.2.2.2.2.2.1
theorem flagData_m : flagData.m = 3 := exists_flagData.choose_spec.2.2.2.2.2.2.1
theorem mem_flagData_Γ (γ : GL (Fin 2) E4) : γ ∈ flagData.Γ ↔ IsUStab gm lat γ ∧
    (∀ v ∈ lat, ∃ w ∈ lat, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) E4) v = v + 3 • w) :=
  exists_flagData.choose_spec.2.2.2.2.2.2.2.1 γ
theorem flagData_χ (la : Wt flagData.Ψ 2) (γ : GL (Fin 2) E4) : flagData.χ la γ = 1 :=
  exists_flagData.choose_spec.2.2.2.2.2.2.2.2 la γ

theorem emb_ii_eq (τ : flagData.Ψ) : τ.1 ii = Complex.I :=
  mem_cmt.1 (flagData_Ψ ▸ τ.2)

theorem norm_ξ0 (τ : flagData.Ψ) : ‖τ.1 flagData.ξ0‖ = 1 / 2 := by
  rw [flagData_ξ0, map_div₀, emb_ii_eq, map_ofNat]
  simp

theorem perfect : (∀ x ∈ flagData.Λ, ∀ y ∈ flagData.Λ, ∃ k : ℤ,
      EFf flagData.ξ0 flagData.Gm x y = k) ∧
    ∀ φ : flagData.Λ →+ ℤ, ∃ x ∈ flagData.Λ, ∀ y : flagData.Λ,
      (φ y : ℚ) = EFf flagData.ξ0 flagData.Gm x y := by
  rw [flagData_Λ, flagData_ξ0, flagData_Gm]
  exact (perfect_iff_traceFormDual_eq half_ii_ne_zero gm_det ⟨lat_fg, lat_span⟩).2 traceFormDual_lat

def cuspData : DataX E4 2 where
  toData := flagData
  k0 := 1
  minWeight_pos := one_pos
  k0_le := one_le_two
  ξ0_abs := norm_ξ0
  EF_int := perfect.1
  EF_perf := perfect.2
  L' := lat
  L'_fg := lat_fg
  L'_int x hx y hy := by rw [flagData_Gm]; exact lat_int hx hy
  L'_dual x h := lat_dual x (by rwa [flagData_Gm] at h)
  NA := 1
  NC := 1
  NA_pos := one_pos
  NC_pos := one_pos
  NA_sub x hx := by rw [flagData_Λ] at hx; simpa using hx
  NC_sub x hx := by rw [flagData_Λ]; simpa using hx
  g := 3
  g_pos := by norm_num
  cong γ h₁ h₂ := by
    rw [flagData_Λ] at h₁ h₂
    rw [flagData_Gm] at h₁
    refine (mem_flagData_Γ γ).2 ⟨h₁, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := h₂ v hv
    exact ⟨w, hw, by rw [← Nat.cast_smul_eq_nsmul E4, ← e]; abel⟩

theorem dom_nonempty : flagData.dom.Nonempty := by
  refine ⟨fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ), fun τ => ?_⟩
  have hm : mat (Ψ := flagData.Ψ) (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) τ = 1 := rfl
  refine ⟨by rw [hm]; simp, fun i => ?_⟩
  unfold dmin
  rw [hm, flagData_Gm, hyperbolicFlagData_base_point, gram_one]
  fin_cases i
  · simp [lminor, psgn]
  · simp [lminor, psgn, sgn]
  · simp [lminor, psgn, sgn, Finset.prod_range_succ, Matrix.det_fin_two]

theorem isIso_one : flagData.IsIso ![1, 1] := by
  refine ⟨?_, ?_, fun h => by simpa using congrFun h 0⟩
  · rw [flagData_Λ]
    intro a
    fin_cases a <;> simpa using isIntegral_one
  · rw [flagData_Gm, herm_gm]
    simp

theorem map_transvMat (v : Fin 2 → E4) (b : E4) (τ : flagData.Ψ) :
    (transvMat flagData.Gm v ((flagData.m : E4) * b * flagData.κ0)).map τ.1 =
      flagData.flowMat v τ (((3 : ℝ) : ℂ) * τ.1 b) := by
  have hc : flagData.c τ = 1 := by rw [Data.c, norm_ξ0]; norm_num
  ext a k
  simp only [transvMat, Data.flowMat, Matrix.map_apply, Matrix.of_apply, hc, flagData_m,
    flagData_κ0, map_add, map_mul, map_sum, map_neg, emb_cc, emb_ii_eq, map_natCast,
    apply_ite τ.1, map_one, map_zero]
  push_cast
  ring

end

end HyperbolicCusp

theorem exists_cuspData_hyperbolic : ∃ (X : DataX E4 2) (M : ℝ),
    X.p0 = 1 ∧ X.dom.Nonempty ∧ (∃ ξ, X.IsIso ξ) ∧ 0 < M ∧ X.Λ = X.L' ∧
    (∀ la, ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E4, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin 2) (Fin 2) E4).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) := by
  refine ⟨HyperbolicCusp.cuspData, 3, HyperbolicCusp.hyperbolicFlagData_base_point, HyperbolicCusp.dom_nonempty,
    ⟨_, HyperbolicCusp.isIso_one⟩, by norm_num, HyperbolicCusp.flagData_Λ,
    fun la v hv hiso b hb hbi => ?_⟩
  obtain ⟨γ, hγ, e⟩ := HyperbolicCusp.flagData.transv v (HyperbolicCusp.flagData_Λ ▸ hv) hiso b hb hbi
  exact ⟨γ, hγ, HyperbolicCusp.flagData_χ la γ, fun τ => by
    rw [e]; exact HyperbolicCusp.map_transvMat v b τ⟩

end GlobalTheory
