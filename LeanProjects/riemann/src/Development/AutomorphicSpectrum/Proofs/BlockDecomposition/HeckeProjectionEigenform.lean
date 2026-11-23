import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection

theorem core {G : Type*} [Group G] (P : G → G → ℂ) (cd : G → ℂ) (K : Subgroup G) (h : G)
    (hI : ∀ t u u', cd t * P (t * u) (t * u') = P u u')
    (hR1 : ∀ κ ∈ K, ∀ u u', P (u * κ) u' = P u u')
    (hR2 : ∀ κ ∈ K, ∀ u u', P u (u' * κ) = P u u')
    (hcd : ∀ κ ∈ K, cd κ = 1)
    (hcomm : ∀ κ ∈ K, κ * h = h * κ)
    {ι : Type*} (B : Finset ι) (t : ι → G) (t₀ t' w : G) (κ : ι → G)
    (hκ : ∀ b ∈ B, κ b ∈ K) (ht : ∀ b ∈ B, t b = κ b * t₀) (hw : w ∈ K) (ht' : t' = w * t₀ * w⁻¹)
    (lam lam' e : ℂ)
    (hs1 : ∑ b ∈ B, P (t b) h + P t' h = lam * P 1 h)
    (hs2 : ∑ b ∈ B, P 1 (h * t b) + P 1 (h * t') = lam' * P 1 h)
    (hz : P 1 (t₀⁻¹ * h) = e * P 1 (h * t'))
    (h0 : P 1 h ≠ 0) : lam = cd t₀⁻¹ * e * lam' := by
  have hm : ∀ k ∈ K, P (k * t₀) h = P t₀ h := fun k hk => by
    have := hI k t₀ h
    rwa [hcd k hk, one_mul, hcomm k hk, hR2 k hk] at this
  have hn : ∀ k ∈ K, P 1 (k * (h * t')) = P 1 (h * t') := fun k hk => by
    have := hI k 1 (h * t')
    rw [hcd k hk, one_mul, mul_one] at this
    have h2 := hR1 k hk 1 (k * (h * t'))
    rw [one_mul] at h2
    rw [← h2, this]
  have e1 : ∀ b ∈ B, P (t b) h = P t₀ h := fun b hb => by rw [ht b hb, hm _ (hκ b hb)]
  have e2 : P t' h = P t₀ h := by rw [ht', hR1 _ (K.inv_mem hw), hm _ hw]
  have e3 : ∀ b ∈ B, P 1 (h * t b) = P 1 (h * t') := fun b hb => by
    have hk : κ b * w⁻¹ ∈ K := K.mul_mem (hκ b hb) (K.inv_mem hw)
    have : h * t b = (κ b * w⁻¹) * (h * t') * w := by
      rw [ht b hb, ← mul_assoc (κ b * w⁻¹), hcomm _ hk, ht']
      group
    rw [this, hR2 _ hw, hn _ hk]
  have e4 := hI t₀⁻¹ t₀ h
  rw [inv_mul_cancel, hz] at e4
  rw [Finset.sum_congr rfl e1, e2, Finset.sum_const, nsmul_eq_mul] at hs1
  rw [Finset.sum_congr rfl e3, Finset.sum_const, nsmul_eq_mul] at hs2
  apply mul_right_cancel₀ h0
  rw [← hs1, ← e4, mul_assoc (cd t₀⁻¹ * e), ← hs2]
  ring

theorem cdet_mul (c : HeckeCharacter ℚ) (g h : G2) : cdet c (g * h) = cdet c g * cdet c h := by
  simp [cdet, map_mul]

theorem norm_cdet (c : HeckeCharacter ℚ) (g : G2) : ‖cdet c g‖ = 1 := by
  exact Circle.norm_coe _

theorem continuous_cdet (c : HeckeCharacter ℚ) : Continuous (cdet c) :=
  continuous_induced_dom.comp (c.continuous_toIdele.comp GeneralLinearGroup.continuous_det)

theorem cdet_dia (c : HeckeCharacter ℚ) (γ : GL (Fin 2) ℚ) : cdet c (dia2 γ) = 1 := by
  have : GeneralLinearGroup.det (dia2 γ) = IdeleGroup.diagonal ℚ (GeneralLinearGroup.det γ) := by
    ext1
    exact (RingHom.map_det (algebraMap ℚ 𝔸[ℚ]) (γ : Matrix (Fin 2) (Fin 2) ℚ)).symm
  simp [cdet, this]

theorem det_diagonal_two (z : Jd) : GeneralLinearGroup.det (dg2 z z : G2) = z * z := by
  ext1
  simp [dg2, Matrix.det_fin_two]

theorem cdet_scal (c : HeckeCharacter ℚ) (z : Jd) : cdet c (dg2 z z) = (c.toIdele z : ℂ) * c.toIdele z := by
  simp [cdet, det_diagonal_two, map_mul]

theorem central_diagonal_commute (z : Jd) (g : G2) : dg2 z z * g = g * dg2 z z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def Fn (φ : G2 → ℂ) (c : HeckeCharacter ℚ) (u u' g : G2) : ℂ := φ (g * u) * conj (φ (g * u')) * cdet c g

def Pr (μ : Measure G2) (𝓕 : Set G2) (φ : G2 → ℂ) (c : HeckeCharacter ℚ) (u u' : G2) : ℂ :=
  ∫ g in 𝓕 ∩ band, Fn φ c u u' g ∂μ

theorem continuous_Fn {φ : G2 → ℂ} (hc : Continuous φ) (c : HeckeCharacter ℚ) (u u' : G2) :
    Continuous (Fn φ c u u') := by
  unfold Fn
  exact ((hc.comp (continuous_mul_const u)).mul
    (Complex.continuous_conj.comp (hc.comp (continuous_mul_const u')))).mul (continuous_cdet c)

theorem norm_Fn_le {φ : G2 → ℂ} {C : ℝ} (hb : ∀ g, ‖φ g‖ ≤ C) (c : HeckeCharacter ℚ) (u u' g : G2) :
    ‖Fn φ c u u' g‖ ≤ C * C := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  unfold Fn
  rw [norm_mul, norm_mul, norm_cdet, mul_one, RCLike.norm_conj]
  exact mul_le_mul (hb _) (hb _) (norm_nonneg _) h0

theorem integrable_Fn {φ : G2 → ℂ} {C : ℝ} (hc : Continuous φ) (hb : ∀ g, ‖φ g‖ ≤ C)
    {μ : Measure G2} {s : Set G2} (hs : μ s < ∞) (c : HeckeCharacter ℚ) (u u' : G2) :
    IntegrableOn (Fn φ c u u') s μ :=
  Measure.integrableOn_of_bounded hs.ne (continuous_Fn hc c u u').aestronglyMeasurable
    (Eventually.of_forall (norm_Fn_le hb c u u'))

theorem Fn_translate (φ : G2 → ℂ) (c : HeckeCharacter ℚ) (t u u' g : G2) :
    Fn φ c u u' (g * t) = cdet c t * Fn φ c (t * u) (t * u') g := by
  simp only [Fn, cdet_mul, mul_assoc]
  ring

section Pair

variable {φ : G2 → ℂ} {ω c : HeckeCharacter ℚ}

theorem circle_mul_conj (w : Circle) : (w : ℂ) * conj (w : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp

theorem toIdele_sq (hc2 : c * c = 1) (z : Jd) : (c.toIdele z : ℂ) * c.toIdele z = 1 := by
  have h := congrArg (fun d : HeckeCharacter ℚ => d.toIdele z) hc2
  have h2 : c.toIdele z * c.toIdele z = 1 := h
  rw [← Circle.coe_mul, h2, Circle.coe_one]

theorem Fn_left (hl : LInv φ) (u u' : G2) : LInv (Fn φ c u u') := fun γ g => by
  simp only [Fn, cdet_mul, cdet_dia, one_mul, mul_assoc (dia2 γ), hl γ]

theorem Fn_scal (hcen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (u u' : G2) (z : Jd) (g : G2) :
    Fn φ c u u' (dg2 z z * g) = (c.toIdele z : ℂ) * c.toIdele z * Fn φ c u u' g := by
  simp only [Fn, cdet_mul, cdet_scal, mul_assoc (dg2 z z), hcen, map_mul]
  have := circle_mul_conj (ω.toIdele z)
  linear_combination (φ (g * u) * conj (φ (g * u')) * ((c.toIdele z : ℂ) * c.toIdele z) * cdet c g) * this

theorem Fn_cinv (hcen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (hc2 : c * c = 1) (u u' : G2) :
    CInv (Fn φ c u u') := fun z g => by
  rw [Fn_scal hcen, toIdele_sq hc2, one_mul]

variable {μ : Measure G2} {𝓕 : Set G2}

theorem Pr_right1 {κ : G2} (hκ : ∀ g, φ (g * κ) = φ g) (u u' : G2) : Pr μ 𝓕 φ c (u * κ) u' = Pr μ 𝓕 φ c u u' := by
  simp only [Pr, Fn, ← mul_assoc, hκ]

theorem Pr_right2 {κ : G2} (hκ : ∀ g, φ (g * κ) = φ g) (u u' : G2) : Pr μ 𝓕 φ c u (u' * κ) = Pr μ 𝓕 φ c u u' := by
  simp only [Pr, Fn, ← mul_assoc, hκ]

theorem Pr_scal (hcen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (z : Jd) (u u' : G2) :
    Pr μ 𝓕 φ c u (dg2 z z * u') = conj (ω.toIdele z : ℂ) * Pr μ 𝓕 φ c u u' := by
  unfold Pr
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [Fn]
  have e : g * (dg2 z z * u') = dg2 z z * (g * u') := by rw [← mul_assoc, ← central_diagonal_commute, mul_assoc]
  rw [e, hcen, map_mul]
  ring

theorem hecke_projection_sum_left {C : ℝ} (hc : Continuous φ) (hb : ∀ g, ‖φ g‖ ≤ C) (hs : μ (𝓕 ∩ band) < ∞)
    {ι : Type*} (B : Finset ι) (t : ι → G2) (t' : G2) (lam : ℂ)
    (hT : ∀ y, ∑ b ∈ B, φ (y * t b) + φ (y * t') = lam * φ y) (u u' : G2) :
    ∑ b ∈ B, Pr μ 𝓕 φ c (u * t b) u' + Pr μ 𝓕 φ c (u * t') u' = lam * Pr μ 𝓕 φ c u u' := by
  unfold Pr
  rw [← integral_finsetSum _ (fun b _ => integrable_Fn hc hb hs c _ _),
    ← integral_add (integrable_finsetSum _ fun b _ => integrable_Fn hc hb hs c _ _) (integrable_Fn hc hb hs c _ _),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [Fn, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← add_mul, hT]

theorem hecke_projection_sum_right {C : ℝ} (hc : Continuous φ) (hb : ∀ g, ‖φ g‖ ≤ C) (hs : μ (𝓕 ∩ band) < ∞)
    {ι : Type*} (B : Finset ι) (t : ι → G2) (t' : G2) (lam : ℂ)
    (hT : ∀ y, ∑ b ∈ B, φ (y * t b) + φ (y * t') = lam * φ y) (u u' : G2) :
    ∑ b ∈ B, Pr μ 𝓕 φ c u (u' * t b) + Pr μ 𝓕 φ c u (u' * t') = conj lam * Pr μ 𝓕 φ c u u' := by
  unfold Pr
  rw [← integral_finsetSum _ (fun b _ => integrable_Fn hc hb hs c _ _),
    ← integral_add (integrable_finsetSum _ fun b _ => integrable_Fn hc hb hs c _ _) (integrable_Fn hc hb hs c _ _),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [Fn, ← mul_assoc]
  have h2 := congrArg conj (hT (g * u'))
  simp only [map_add, map_sum, map_mul] at h2
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← add_mul, ← mul_add, h2]
  ring

theorem Pr_translate {C : ℝ} (hc : Continuous φ) (hb : ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hcen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (hc2 : c * c = 1)
    (hG : ∀ F : G2 → ℂ, Continuous F → (∃ C, ∀ g, ‖F g‖ ≤ C) → LInv F → CInv F →
      ∀ h, ∫ g in 𝓕 ∩ band, F (g * h) ∂μ = ∫ g in 𝓕 ∩ band, F g ∂μ) (t u u' : G2) :
    cdet c t * Pr μ 𝓕 φ c (t * u) (t * u') = Pr μ 𝓕 φ c u u' := by
  have := hG (Fn φ c u u') (continuous_Fn hc c u u') ⟨_, norm_Fn_le hb c u u'⟩ (Fn_left hl u u') (Fn_cinv hcen hc2 u u') t
  simp only [Fn_translate] at this
  rw [integral_const_mul] at this
  exact this

end Pair

section Local

open GroundTheory.Automorphic.Reduction in
theorem isLoc2_mul {v : Pl} {x y : GL (Fin 2) (Qv v)} {h h' : G2} (hx : IsLoc2 v x h) (hy : IsLoc2 v y h') :
    IsLoc2 v (x * y) (h * h') :=
  ⟨by rw [finAt_mul, hx.1, hy.1], fun v' hv' => by rw [finAt_mul, hx.2.1 v' hv', hy.2.1 v' hv', one_mul],
    fun w => by rw [infAt_mul, hx.2.2 w, hy.2.2 w, one_mul]⟩

theorem isLoc2_unique {v : Pl} {x : GL (Fin 2) (Qv v)} {h h' : G2}
    (hext : ∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g')
    (hx : IsLoc2 v x h) (hy : IsLoc2 v x h') : h = h' := by
  refine hext _ _ (fun v' => ?_) (fun w => by rw [hx.2.2 w, hy.2.2 w])
  by_cases e : v' = v
  · subst e; rw [hx.1, hy.1]
  · rw [hx.2.1 v' e, hy.2.1 v' e]

open GroundTheory.Automorphic.Reduction in
theorem isLoc2_comm {v : Pl} {x : GL (Fin 2) (Qv v)} {k h : G2}
    (hext : ∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g')
    (hx : IsLoc2 v x k) (hv : finAt v h = 1) : k * h = h * k := by
  refine hext _ _ (fun v' => ?_) (fun w => by simp [infAt_mul, hx.2.2 w])
  rw [finAt_mul, finAt_mul]
  by_cases e : v' = v
  · subst e; rw [hv, mul_one, one_mul]
  · rw [hx.2.1 v' e, one_mul, mul_one]

open GroundTheory.Automorphic.Reduction in

theorem det_eq_of_comps {h h' : G2}
    (hf : ∀ v : Pl, GeneralLinearGroup.det (finAt v h) = GeneralLinearGroup.det (finAt v h'))
    (hi : ∀ w, GeneralLinearGroup.det (infAt w h) = GeneralLinearGroup.det (infAt w h')) :
    GeneralLinearGroup.det h = GeneralLinearGroup.det h' := by
  have e1 : ∀ (v : Pl) (g : G2), ((GeneralLinearGroup.det g : (𝔸[ℚ])ˣ) : 𝔸[ℚ]).2 v =
      ((GeneralLinearGroup.det (finAt v g) : (Qv v)ˣ) : Qv v) := fun v g =>
    RingHom.map_det (finEval v) (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
  have e2 : ∀ (w : InfinitePlace ℚ) (g : G2), ((GeneralLinearGroup.det g : (𝔸[ℚ])ˣ) : 𝔸[ℚ]).1 w =
      ((GeneralLinearGroup.det (infAt w g) : (w.Completion)ˣ) : w.Completion) := fun w g =>
    RingHom.map_det (infEval w) (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun v => ?_))
  · rw [e2, e2, hi]
  · exact (e1 v h).trans ((congrArg _ (hf v)).trans (e1 v h').symm)

end Local

theorem pure_conj {k N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℕ → ℂ} (hp : Pure k N χ a) {p : ℕ} (pp : p.Prime)
    (hN : ¬ p ∣ N) (hχ : ‖χ p‖ = 1) : χ p * conj (a p) = a p := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a p) ^ 2 - 4 * (χ p * (p : ℂ) ^ (k - 1))) (n := 2) (by norm_num)
  set α : ℂ := (a p + z) / 2 with hα
  set β : ℂ := (a p - z) / 2 with hβ
  have hs : α + β = a p := by rw [hα, hβ]; ring
  have hm : α * β = χ p * (p : ℂ) ^ (k - 1) := by
    rw [hα, hβ]; linear_combination (-1 / 4 : ℂ) * hz
  have hn := hp p pp hN α β hs hm
  have hQ0 : ((p : ℂ) ^ (k - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast pp.ne_zero)
  have hnorm : ‖α‖ * ‖β‖ = (p : ℝ) ^ (k - 1) := by
    rw [← norm_mul, hm, norm_mul, hχ, one_mul, norm_pow, Complex.norm_natCast]
  have hA : α * conj α = (p : ℂ) ^ (k - 1) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]
    nth_rewrite 2 [hn]
    rw [hnorm]; push_cast; rfl
  have hB : β * conj β = (p : ℂ) ^ (k - 1) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]
    nth_rewrite 1 [← hn]
    rw [hnorm]; push_cast; rfl
  have e1 : β = χ p * conj α := by
    apply mul_left_cancel₀ hQ0
    linear_combination (-β) * hA + conj α * hm
  have e2 : α = χ p * conj β := by
    apply mul_left_cancel₀ hQ0
    linear_combination (-α) * hB + conj β * hm
  rw [← hs, map_add, mul_add, ← e1, ← e2, add_comm]

section Key

theorem det_diag_adelic_GL2 {R : Type*} [CommRing R] (a d : Rˣ) : GeneralLinearGroup.det (dg2 a d) = a * d := by
  ext1
  simp [dg2, Matrix.det_fin_two]

theorem diagonal_mul_diagonal_alt {R : Type*} [CommRing R] (a b c d : Rˣ) :
    (dg2 a b * dg2 c d : GL (Fin 2) R) = dg2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_diagonal_one_one {R : Type*} [CommRing R] : (dg2 1 1 : GL (Fin 2) R) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem antidiagonal_torus_weyl_conjugate {R : Type*} [CommRing R] (a : Rˣ) :
    (dg2 1 a : GL (Fin 2) R) = w0 * dg2 a 1 * w0⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, w0, Matrix.mul_apply, Fin.sum_univ_two]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unipotent_integral_mem_compact {y : F} (hy : y ∈ 𝒪[F]) : uni2 y ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have hn : -y ∈ 𝒪[F] := neg_mem hy
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [uni2, hy, hn, zero_mem, one_mem]

theorem cmHalfIntegralGenerator_mem_algebraicClosure : (w0 : GL (Fin 2) F) ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have hn : (-1 : F) ∈ 𝒪[F] := neg_mem (one_mem _)
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [w0, hn, zero_mem, one_mem]

theorem ord_det_of_mem {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) :
    ord ((GeneralLinearGroup.det x : Fˣ) : F) = 0 :=
  GroundTheory.Automorphic.GodementJacquet.ordDet_of_mem_integralGL hx

end Key

open GroundTheory.Automorphic.Reduction in

theorem eig_relation {φ : G2 → ℂ} {ω c : HeckeCharacter ℚ} {μ : Measure G2} {𝓕 : Set G2} {C : ℝ}
    (hc : Continuous φ) (hb : ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hcen : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (hc2 : c * c = 1)
    (hG : ∀ F : G2 → ℂ, Continuous F → (∃ C, ∀ g, ‖F g‖ ≤ C) → LInv F → CInv F →
      ∀ h, ∫ g in 𝓕 ∩ band, F (g * h) ∂μ = ∫ g in 𝓕 ∩ band, F g ∂μ)
    (hs : μ (𝓕 ∩ band) < ∞) {v : Pl} (hloc : ∀ x, ∃ h, IsLoc2 v x h)
    (hext : ∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g')
    (hlast : ∀ (x : Qv v) (a d : (Qv v)ˣ), ∃ (x' : 𝔸[ℚ]) (a' d' : Jd), IsLoc2 v (uni2 x) (uni2 x') ∧
      IsLoc2 v (dg2 a d) (dg2 a' d') ∧ adelicChar ℚ x' = localAdelicChar ℚ v x ∧ (a = d → a' = d') ∧
      ∀ c : HeckeCharacter ℚ, (c.toIdele a' : ℂ) = localChar c v a ∧ (c.toIdele d' : ℂ) = localChar c v d)
    (hcu : IsUnramifiedChar (localChar c v)) {lam : ℂ} (hT : ∀ g W, LocFn v φ g W → TypeT lam W)
    {ϖ : (Qv v)ˣ} {B : Finset (Qv v)} (hR : Reps ϖ B) {h : G2} (hv : finAt v h = 1)
    (h0 : Pr μ 𝓕 φ c 1 h ≠ 0) :
    lam = ((localChar c v ϖ⁻¹ : ℂˣ) : ℂ) * ((localChar ω v ϖ : ℂˣ) : ℂ) * conj lam := by
  choose L hL using hloc
  have hLm : ∀ x y, L (x * y) = L x * L y := fun x y =>
    isLoc2_unique hext (hL _) (isLoc2_mul (hL x) (hL y))
  have hL1 : L 1 = 1 := isLoc2_unique hext (hL 1) ⟨finAt_one v, fun v' _ => finAt_one v', fun w => infAt_one w⟩
  let Lh : GL (Fin 2) (Qv v) →* G2 := { toFun := L, map_one' := hL1, map_mul' := hLm }
  have hLh : ∀ x, Lh x = L x := fun _ => rfl
  have hLinv : ∀ x, L x⁻¹ = (L x)⁻¹ := fun x => map_inv Lh x
  have hTT : ∀ g, TypeT lam (fun x => φ (g * L x)) := fun g => hT g _ fun x h' hx => by
    rw [isLoc2_unique hext hx (hL x)]
  have hsph : ∀ x ∈ integralGL (Qv v) 2, ∀ g, φ (g * L x) = φ g := fun x hx g => by
    have := (hTT g).1 x hx 1
    simpa [hL1] using this
  have hTs : ∀ y, ∑ b ∈ B, φ (y * L (upm ϖ b)) + φ (y * L (dg2 1 ϖ)) = lam * φ y := fun y => by
    have := (hTT y).2 ϖ B hR 1
    simpa [hL1] using this
  have hcL : ∀ x, cdet c (L x) = localChar c v (GeneralLinearGroup.det x) := fun x => by
    obtain ⟨_, a', d', -, hd, -, -, hch⟩ := hlast 0 (GeneralLinearGroup.det x) 1
    have e : GeneralLinearGroup.det (L x) = GeneralLinearGroup.det (dg2 a' d' : G2) := by
      refine det_eq_of_comps (fun v' => ?_) (fun w => ?_)
      · by_cases e : v' = v
        · subst e; rw [(hL x).1, hd.1, det_diag_adelic_GL2, mul_one]
        · rw [(hL x).2.1 v' e, hd.2.1 v' e]
      · rw [(hL x).2.2 w, hd.2.2 w]
    have h2 := (hch c).2
    rw [map_one, Units.val_one] at h2
    rw [cdet, e, det_diag_adelic_GL2, map_mul, Circle.coe_mul, (hch c).1, h2, mul_one]
  let K : Subgroup G2 := (integralGL (Qv v) 2).map Lh
  have hKs : ∀ κ ∈ K, ∀ g, φ (g * κ) = φ g := by
    rintro _ ⟨x, hx, rfl⟩ g
    exact hsph x hx g
  have hI := fun t u u' => Pr_translate (μ := μ) (𝓕 := 𝓕) hc hb hl hcen hc2 hG t u u'
  have hmain := core (Pr μ 𝓕 φ c) (cdet c) K h hI (fun κ hκ u u' => Pr_right1 (hKs κ hκ) u u')
    (fun κ hκ u u' => Pr_right2 (hKs κ hκ) u u')
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [hLh, hcL, isUnramifiedChar_iff.1 hcu _ (ord_det_of_mem hx), Units.val_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact isLoc2_comm hext (hL x) hv)
    B (fun b => L (upm ϖ b)) (L (dg2 ϖ 1)) (L (dg2 1 ϖ)) (L w0) (fun b => L (uni2 b))
    (fun b hb => ⟨uni2 b, unipotent_integral_mem_compact (hR.2.1 b hb), rfl⟩)
    (fun b _ => by rw [upm, hLm])
    ⟨w0, cmHalfIntegralGenerator_mem_algebraicClosure, rfl⟩
    (by rw [antidiagonal_torus_weyl_conjugate, hLm, hLm, hLinv])
    lam (conj lam) (conj (((localChar ω v ϖ⁻¹ : ℂˣ) : ℂ)))
    (by
      have := hecke_projection_sum_left (c := c) (μ := μ) (𝓕 := 𝓕) hc hb hs B (fun b => L (upm ϖ b)) (L (dg2 1 ϖ)) lam hTs 1 h
      simpa using this)
    (hecke_projection_sum_right (c := c) (μ := μ) (𝓕 := 𝓕) hc hb hs B (fun b => L (upm ϖ b)) (L (dg2 1 ϖ)) lam hTs 1 h)
    (by
      obtain ⟨_, z, z', -, hd, -, hzz, hch⟩ := hlast 0 ϖ⁻¹ ϖ⁻¹
      obtain rfl := hzz rfl
      have e1 : dg2 ϖ⁻¹ ϖ⁻¹ * dg2 1 ϖ = (dg2 ϖ 1)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        simp only [diagonal_mul_diagonal_alt, mul_one, inv_mul_cancel, scalar_diagonal_one_one]
      have e2 : (L (dg2 ϖ 1))⁻¹ * h = dg2 z z * (h * L (dg2 1 ϖ)) := by
        rw [← hLinv, ← e1, hLm, isLoc2_unique hext (hL _) hd, mul_assoc,
          isLoc2_comm hext (hL _) hv]
      rw [e2, Pr_scal hcen, (hch ω).1])
    h0
  have e3 : cdet c (L (dg2 ϖ 1))⁻¹ = ((localChar c v ϖ⁻¹ : ℂˣ) : ℂ) := by
    rw [← hLinv, hcL, map_inv, det_diag_adelic_GL2, mul_one, map_inv]
  have e4 : conj ((localChar ω v ϖ⁻¹ : ℂˣ) : ℂ) = ((localChar ω v ϖ : ℂˣ) : ℂ) := by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar, GroundTheory.Automorphic.GodementSection.coe_localChar, map_inv,
      Circle.coe_inv_eq_conj, Complex.conj_conj]
  rw [e3, e4] at hmain
  exact hmain

theorem toIdele_mul (c d : HeckeCharacter ℚ) (z : Jd) :
    (((c * d).toIdele z : Circle) : ℂ) = (c.toIdele z : ℂ) * d.toIdele z := rfl

theorem g6 : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6 := by
  intro hB hC hG hF0b hF1 hF3 hF5
  intro k N _ hk χ hχ f a hf ha ω φ hOm hLift hPure μ 𝓕 mK 𝓓 hSet S hS c hcf hc1 hcu x h hUn hne
  obtain ⟨hBv, -, -, hext, -, -, -, hlast⟩ := hB
  obtain ⟨hsign, -⟩ := hF1 k N χ f a hf ha.2.1 ω hOm
  have hOL := hF0b k N χ hχ hsign ω hOm
  obtain ⟨⟨C, hC'⟩, -⟩ := hF5 k N hk χ hχ f a hf ha ω φ hOm hLift
  have hH : Hk k N a ω φ := hF3 k N hk χ hχ f a hf ha ω φ hOm hLift
  have hc := hLift.cont
  have hl := hLift.left
  have hcen := hLift.cen
  have h1 := hG μ 𝓕 mK 𝓓 hSet
  have hP0 : Pr μ 𝓕 φ c 1 h ≠ 0 := by simpa [Pr, Fn] using hne
  have hc2 : c * c = 1 := by
    by_contra hne2
    apply hP0
    refine (h1 (Fn φ c 1 h) (continuous_Fn hc c 1 h) ⟨_, norm_Fn_le hC' c 1 h⟩ (Fn_left hl 1 h)).2.1 (c * c)
      (by rw [← pow_two]; exact hcf.pow) (fun z g => ?_) hne2
    rw [Fn_scal hcen, toIdele_mul]
  have hG' : ∀ F : G2 → ℂ, Continuous F → (∃ C, ∀ g, ‖F g‖ ≤ C) → LInv F → CInv F →
      ∀ h, ∫ g in 𝓕 ∩ band, F (g * h) ∂μ = ∫ g in 𝓕 ∩ band, F g ∂μ :=
    fun F a1 a2 a3 a4 h' => (h1 F a1 a2 a3).1 a4 h'
  refine ⟨c, hc1, by rw [pow_two, hc2], ?_⟩
  filter_upwards [S.finite_toSet.eventually_cofinite_notMem] with v hv
  have hvS : v ∉ S := fun e => hv e
  have hvN : ¬ pOf v ∣ N := fun e => hvS (hS v e)
  refine ⟨hcu v hvS, ?_⟩
  obtain ⟨hstd, -, hpr, -, -, hloc, -⟩ := hBv v
  obtain ⟨ϖ, B, hR⟩ := (hC (Qv v) (localAdelicChar ℚ v) hstd).1
  have hrel := eig_relation hc hC' hl hcen hc2 hG' hSet.vol hloc hext (hlast v) (hcu v hvS) (hH.good v hvN) hR
    (hUn.2.1 v hvS) hP0
  obtain ⟨hωu, hωχ⟩ := hOL.good v hvN
  have e1 : localChar ω v ϖ = localChar ω v (unifUnit (Qv v)) := quasiChar_apply_eq_of_isUnramified hωu hR.1
  have e2 : localChar c v ϖ = localChar c v (unifUnit (Qv v)) := quasiChar_apply_eq_of_isUnramified (hcu v hvS) hR.1
  have hχn : ‖χ (pOf v)‖ = 1 := by
    rw [← hωχ, GroundTheory.Automorphic.GodementSection.coe_localChar]
    exact Circle.norm_coe _
  have hconj := pure_conj hPure hpr hvN hχn
  rw [e1, hωχ] at hrel
  by_cases ha0 : a (pOf v) = 0
  · exact Or.inr ha0
  left
  set r : ℝ := (pOf v : ℝ) ^ (1 - (k : ℝ) / 2) with hr
  have hr0 : (r : ℂ) ≠ 0 := by
    have : r ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hpr.pos) _).ne'
    exact_mod_cast this
  have e3 : ((localChar c v ϖ⁻¹ : ℂˣ) : ℂ) = 1 := by
    have e4 : lamOf k a v = a (pOf v) * (r : ℂ) := rfl
    rw [e4, map_mul, Complex.conj_ofReal] at hrel
    have e5 : a (pOf v) * (r : ℂ) * (((localChar c v ϖ⁻¹ : ℂˣ) : ℂ) - 1) = 0 := by
      linear_combination (-1 : ℂ) * hrel + ((localChar c v ϖ⁻¹ : ℂˣ) : ℂ) * (r : ℂ) * hconj * (-1 : ℂ)
    rcases mul_eq_zero.1 e5 with e6 | e6
    · exact absurd e6 (mul_ne_zero ha0 hr0)
    · exact sub_eq_zero.1 e6
  rw [← e2]
  have e7 : localChar c v ϖ⁻¹ = 1 := Units.ext e3
  rw [map_inv] at e7
  exact inv_eq_one.1 e7

end GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection

end
