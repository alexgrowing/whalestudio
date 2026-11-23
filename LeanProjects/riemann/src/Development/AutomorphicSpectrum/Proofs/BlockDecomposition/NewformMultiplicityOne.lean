import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinTestVector

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open Classical in

def gU (μ : Fˣ →* ℂˣ) (y : F) : ℂ :=
  if h : y ≠ 0 ∧ ord y = 0 then ((μ (Units.mk0 y h.1) : ℂˣ) : ℂ) else 0

theorem gU_unit (μ : Fˣ →* ℂˣ) (u : Fˣ) (hu : ord (u : F) = 0) : gU μ (u : F) = ((μ u : ℂˣ) : ℂ) := by
  have h : (u : F) ≠ 0 ∧ ord (u : F) = 0 := ⟨u.ne_zero, hu⟩
  rw [gU, dif_pos h, Units.mk0_val]

theorem gU_eq_zero (μ : Fˣ →* ℂˣ) {y : F} (h : ¬ (y ≠ 0 ∧ ord y = 0)) : gU μ y = 0 := dif_neg h

theorem unit_add {y t : F} {n : ℕ} (hn : 1 ≤ n) (hy : y ≠ 0) (h0 : ord y = 0)
    (ht : t ∈ valBall F n) : y + t ≠ 0 ∧ ord (y + t) = 0 := by
  have h1 : t ∈ valBall F (ord y + 1) := by
    rw [h0]
    exact valBall_antitone (by omega) ht
  obtain ⟨h2, h3⟩ := ord_add_eq hy h1
  exact ⟨h2, h3.trans h0⟩

theorem inv_mem_ball {y : F} (hy : y ≠ 0) (h0 : ord y = 0) : y⁻¹ ∈ valBall F 0 := by
  rw [mem_valBall_iff_le_ord (inv_ne_zero hy), ord_inv hy, h0]
  simp

theorem gU_add {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n) (hk : unitFiltrationUnits F n ≤ μ.ker)
    (y : F) {t : F} (ht : t ∈ valBall F n) : gU μ (y + t) = gU μ y := by
  by_cases hy : y ≠ 0 ∧ ord y = 0
  · obtain ⟨h1, h2⟩ := unit_add hn hy.1 hy.2 ht
    have hv : (Units.mk0 y hy.1)⁻¹ * Units.mk0 (y + t) h1 ∈ unitFiltrationUnits F n := by
      rw [mem_unitFiltrationUnits_iff_valBall hn]
      have e : (((Units.mk0 y hy.1)⁻¹ * Units.mk0 (y + t) h1 : Fˣ) : F) - 1 = y⁻¹ * t := by
        have := hy.1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
        ring
      rw [e]
      have := mul_mem_valBall (inv_mem_ball hy.1 hy.2) ht
      simpa using this
    have hb : μ (Units.mk0 (y + t) h1) = μ (Units.mk0 y hy.1) := by
      have := hk hv
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    rw [gU, gU, dif_pos ⟨h1, h2⟩, dif_pos hy, hb]
  · have h3 : ¬ (y + t ≠ 0 ∧ ord (y + t) = 0) := fun h => hy (by
      have := unit_add hn h.1 h.2 (neg_mem ht)
      simpa using this)
    rw [gU_eq_zero μ h3, gU_eq_zero μ hy]

theorem gU_mul (μ : Fˣ →* ℂˣ) (u : Fˣ) (hu : ord (u : F) = 0) (y : F) :
    gU μ ((u : F) * y) = ((μ u : ℂˣ) : ℂ) * gU μ y := by
  by_cases hy : y ≠ 0 ∧ ord y = 0
  · have e : (u : F) * y = ((u * Units.mk0 y hy.1 : Fˣ) : F) := by simp
    have hv : ord ((u * Units.mk0 y hy.1 : Fˣ) : F) = 0 := by
      rw [ord_units_mul, hu, Units.val_mk0, hy.2]; rfl
    have e2 : y = ((Units.mk0 y hy.1 : Fˣ) : F) := rfl
    rw [e, gU_unit μ _ hv, map_mul, Units.val_mul]
    conv_rhs => rw [e2, gU_unit μ _ (by rw [Units.val_mk0]; exact hy.2)]
  · have h3 : ¬ ((u : F) * y ≠ 0 ∧ ord ((u : F) * y) = 0) := fun h => hy (by
      have hy0 : y ≠ 0 := right_ne_zero_of_mul h.1
      refine ⟨hy0, ?_⟩
      have := h.2
      rw [ord_mul u.ne_zero hy0, hu] at this
      simpa using this)
    rw [gU_eq_zero μ h3, gU_eq_zero μ hy, mul_zero]

theorem gU_mem {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n) (hk : unitFiltrationUnits F n ≤ μ.ker) :
    gU μ ∈ schwartzBruhat F := by
  refine ⟨isLocallyConstant_of_add_valBall (N := n) fun x h hh => gU_add hn hk x hh, ?_⟩
  refine HasCompactSupport.intro (isCompact_valBall 0) fun y hy => gU_eq_zero μ fun h => hy ?_
  rw [SetLike.mem_coe, mem_valBall_iff_le_ord h.1, h.2]

def fB (n : ℕ) : F → ℂ := (valBall F (n : ℤ) : Set F).indicator fun _ => (1 : ℂ)

theorem fB_mem (n : ℕ) : (fB n : F → ℂ) ∈ schwartzBruhat F := indicator_valBall_mem_schwartzBruhat _

def phi0 (n : ℕ) (μ : Fˣ →* ℂˣ) : (Fin 2 → F) → ℂ := Ad3.SchwartzSpaceL2.pt (fB n) (gU μ)

theorem fB_ne {n : ℕ} {y : F} (h : fB n y ≠ 0) : y ∈ valBall F (n : ℤ) := by
  by_contra hy
  exact h (Set.indicator_of_notMem hy _)

theorem fB_of_mem {n : ℕ} {y : F} (h : y ∈ valBall F (n : ℤ)) : fB n y = 1 :=
  Set.indicator_of_mem (show y ∈ (valBall F (n : ℤ) : Set F) from h) _

theorem fB_of_notMem {n : ℕ} {y : F} (h : y ∉ valBall F (n : ℤ)) : fB n y = 0 :=
  Set.indicator_of_notMem h _

theorem gU_ne {μ : Fˣ →* ℂˣ} {y : F} (h : gU μ y ≠ 0) : y ≠ 0 ∧ ord y = 0 := by
  by_contra hy
  exact h (gU_eq_zero μ hy)

theorem test_vector_mem_schwartz_bruhat {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n) (hk : unitFiltrationUnits F n ≤ μ.ker) :
    phi0 n μ ∈ GodementSectionLocal.schwartzBruhat2 F := by
  have h1 := (fB_mem (F := F) n).1
  have h2 := (gU_mem hn hk).1
  refine ⟨(h1.comp_continuous (continuous_apply 0)).mul (h2.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro (GodementSectionLocal.isCompact_box 0) fun r hr => ?_
  by_contra hne
  apply hr
  have h3 : fB n (r 0) ≠ 0 := left_ne_zero_of_mul hne
  have h4 : gU μ (r 1) ≠ 0 := right_ne_zero_of_mul hne
  refine GodementSectionLocal.mem_box.2 fun i => ?_
  fin_cases i
  · exact valBall_antitone (by omega) (fB_ne h3)
  · have h5 := gU_ne h4
    show r 1 ∈ valBall F 0
    rw [mem_valBall_iff_le_ord h5.1, h5.2]

def Sup (n : ℕ) (r : Fin 2 → F) : Prop := r 0 ∈ valBall F (n : ℤ) ∧ r 1 ≠ 0 ∧ ord (r 1) = 0

theorem support_of_test_vector {n : ℕ} {μ : Fˣ →* ℂˣ} {r : Fin 2 → F} (h : phi0 n μ r ≠ 0) : Sup n r := by
  have h3 : fB n (r 0) ≠ 0 := left_ne_zero_of_mul h
  have h4 : gU μ (r 1) ≠ 0 := right_ne_zero_of_mul h
  exact ⟨fB_ne h3, gU_ne h4⟩

theorem int_ball {x : F} (h : x ∈ 𝒪[F]) : x ∈ valBall F 0 := mem_valBall_zero_iff.2 h

theorem diag_unit {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2)
    (hc : x 1 0 ∈ valBall F 1) : x 0 0 ≠ 0 ∧ ord (x 0 0) = 0 ∧ x 1 1 ≠ 0 ∧ ord (x 1 1) = 0 := by
  obtain ⟨hx1, -⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  have hd := GodementSectionLocal.ord_det_eq_zero hx
  have hdet : ((GodementSectionLocal.detU x : Fˣ) : F) = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    show ((Matrix.GeneralLinearGroup.det x : Fˣ) : F) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hb : x 0 1 * x 1 0 ∈ valBall F (1 : ℕ) := by
    have := mul_mem_valBall (int_ball (hx1 0 1)) hc
    simpa using this
  obtain ⟨h1, h2⟩ := unit_add (n := 1) le_rfl (GodementSectionLocal.detU x).ne_zero hd hb
  rw [hdet, sub_add_cancel] at h1 h2
  have ha : x 0 0 ≠ 0 := left_ne_zero_of_mul h1
  have hdd : x 1 1 ≠ 0 := right_ne_zero_of_mul h1
  rw [ord_mul ha hdd] at h2
  have h3 := GodementSectionLocal.ord_nonneg_of_mem_integers ha (hx1 0 0)
  have h4 := GodementSectionLocal.ord_nonneg_of_mem_integers hdd (hx1 1 1)
  exact ⟨ha, by omega, hdd, by omega⟩

theorem vecMul_0 (r : Fin 2 → F) (x : GL (Fin 2) F) :
    (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) 0 = r 0 * x 0 0 + r 1 * x 1 0 := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_1 (r : Fin 2 → F) (x : GL (Fin 2) F) :
    (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) 1 = r 0 * x 0 1 + r 1 * x 1 1 := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem sup_mul {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2)
    (hc : x 1 0 ∈ valBall F (n : ℤ)) {r : Fin 2 → F} (hr : Sup n r) :
    Sup n (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) := by
  obtain ⟨hx1, -⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  obtain ⟨-, -, hd0, hd1⟩ := diag_unit hx (valBall_antitone (by omega) hc)
  obtain ⟨h0, h1, h2⟩ := hr
  have hr1 : r 1 ∈ valBall F 0 := by rw [mem_valBall_iff_le_ord h1, h2]
  have hA : r 0 * x 0 0 ∈ valBall F (n : ℤ) := by
    simpa using mul_mem_valBall h0 (int_ball (hx1 0 0))
  have hB : r 1 * x 1 0 ∈ valBall F (n : ℤ) := by
    simpa using mul_mem_valBall hr1 hc
  have hC : r 0 * x 0 1 ∈ valBall F (n : ℤ) := by
    simpa using mul_mem_valBall h0 (int_ball (hx1 0 1))
  obtain ⟨h3, h4⟩ := unit_add hn (mul_ne_zero h1 hd0) (by rw [ord_mul h1 hd0, h2, hd1]; rfl) hC
  refine ⟨?_, ?_, ?_⟩
  · rw [vecMul_0]
    exact add_mem hA hB
  · rw [vecMul_1, add_comm]
    exact h3
  · rw [vecMul_1, add_comm]
    exact h4

theorem test_vector_congruence_equivariance_support {n : ℕ} (hn : 1 ≤ n) {μ : Fˣ →* ℂˣ} (hk : unitFiltrationUnits F n ≤ μ.ker)
    {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2) (hc : x 1 0 ∈ valBall F (n : ℤ))
    {d : Fˣ} (hd : (d : F) = x 1 1) {r : Fin 2 → F} (hr : Sup n r) :
    phi0 n μ (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) = ((μ d : ℂˣ) : ℂ) * phi0 n μ r := by
  obtain ⟨hx1, -⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  obtain ⟨-, -, hd0, hd1⟩ := diag_unit hx (valBall_antitone (by omega) hc)
  have h5 := sup_mul hn hx hc hr
  have hC : r 0 * x 0 1 ∈ valBall F (n : ℤ) := by
    simpa using mul_mem_valBall hr.1 (int_ball (hx1 0 1))
  simp only [phi0, Ad3.SchwartzSpaceL2.pt]
  rw [fB_of_mem h5.1, fB_of_mem hr.1, vecMul_1, add_comm, gU_add hn hk _ hC, mul_comm (r 1), ← hd,
    gU_mul μ d (by rw [hd]; exact hd1)]
  ring

theorem inv_ball {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2)
    (hc : x 1 0 ∈ valBall F (n : ℤ)) : (x⁻¹ : GL (Fin 2) F) 1 0 ∈ valBall F (n : ℤ) := by
  obtain ⟨-, hx2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  obtain ⟨ha0, ha1, -, -⟩ := diag_unit hx (valBall_antitone (by omega) hc)
  have e : (((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
    rw [← Units.val_mul, inv_mul_cancel]
    simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at e
  have e2 : (x⁻¹ : GL (Fin 2) F) 1 0 = (x 0 0)⁻¹ * (-((x⁻¹ : GL (Fin 2) F) 1 1 * x 1 0)) := by
    have : (x⁻¹ : GL (Fin 2) F) 1 0 * x 0 0 = -((x⁻¹ : GL (Fin 2) F) 1 1 * x 1 0) := eq_neg_of_add_eq_zero_left e
    rw [← this]
    field_simp
  rw [e2]
  have h1 : (x⁻¹ : GL (Fin 2) F) 1 1 * x 1 0 ∈ valBall F (n : ℤ) := by
    simpa using mul_mem_valBall (int_ball (hx2 1 1)) hc
  simpa using mul_mem_valBall (inv_mem_ball ha0 ha1) (neg_mem h1)

theorem test_vector_congruence_equivariance {n : ℕ} (hn : 1 ≤ n) {μ : Fˣ →* ℂˣ} (hk : unitFiltrationUnits F n ≤ μ.ker)
    {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2) (hc : x 1 0 ∈ valBall F (n : ℤ))
    {d : Fˣ} (hd : (d : F) = x 1 1) (r : Fin 2 → F) :
    phi0 n μ (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) = ((μ d : ℂˣ) : ℂ) * phi0 n μ r := by
  by_cases hr : Sup n r
  · exact test_vector_congruence_equivariance_support hn hk hx hc hd hr
  · have h0 : phi0 n μ r = 0 := by
      by_contra h
      exact hr (support_of_test_vector h)
    rw [h0, mul_zero]
    by_contra h
    apply hr
    have := sup_mul hn (inv_mem hx) (inv_ball hn hx hc) (support_of_test_vector h)
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this
    exact this

theorem lower_left_entry_mem_ball {n : ℕ} {x : GL (Fin 2) F} {d : Fˣ} (h : Ad3.R.GammaZeroLevelMembership n x d) :
    x 1 0 ∈ valBall F (n : ℤ) := by
  have h1 : (((unifUnit F ^ n : Fˣ)) : F) ∈ valBall F (n : ℤ) := by
    have := mem_valBall_ord (K := F) (x := ((unifUnit F ^ (n : ℤ) : Fˣ) : F))
    rw [ord_unifUnit_zpow] at this
    simpa using this
  have h2 := mul_mem_valBall h1 (int_ball h.2.1)
  have e : ((unifUnit F ^ n : Fˣ) : F) * ((((unifUnit F)⁻¹ ^ n : Fˣ) : F) * x 1 0) = x 1 0 := by
    rw [← mul_assoc, ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one, one_mul]
  rw [e] at h2
  simpa using h2

theorem val_ball_one {ϖ : Fˣ} (h1 : ord (ϖ : F) = 1) {z : F} (hz : ((ϖ⁻¹ : Fˣ) : F) * z ∈ 𝒪[F]) :
    z ∈ valBall F 1 := by
  have h2 : (ϖ : F) ∈ valBall F 1 := by
    rw [mem_valBall_iff_le_ord ϖ.ne_zero, h1]
  have h3 := mul_mem_valBall h2 (int_ball hz)
  have e : (ϖ : F) * (((ϖ⁻¹ : Fˣ) : F) * z) = z := by
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [e] at h3
  simpa using h3

theorem unit_int {u : Fˣ} (hu : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord u.ne_zero, hu]

theorem unit_inv_int {u : Fˣ} (hu : ord (u : F) = 0) : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
  rw [← mem_valBall_zero_iff, Units.val_inv_eq_inv_val]
  exact inv_mem_ball u.ne_zero hu

theorem sum_affine {ϖ : Fˣ} {B : Finset F} (hB : Ad3.R.Reps ϖ B) {u : Fˣ} (hu : ord (u : F) = 0)
    {c : F} (hc : c ∈ 𝒪[F]) (G : F → ℂ) (hG : ∀ t, ∀ s ∈ valBall F 1, G (t + s) = G t) :
    ∑ b ∈ B, G (c + u * b) = ∑ b ∈ B, G b := by
  classical
  obtain ⟨h1, h2, h3⟩ := hB
  have hex : ∀ b ∈ B, ∃ b', b' ∈ B ∧ ((ϖ⁻¹ : Fˣ) : F) * (c + u * b - b') ∈ 𝒪[F] := fun b hb =>
    (h3 _ (add_mem hc (mul_mem (unit_int hu) (h2 b hb)))).exists
  choose! σ hσ1 hσ2 using hex
  have hGσ : ∀ b ∈ B, G (c + u * b) = G (σ b) := by
    intro b hb
    have := hG (σ b) _ (val_ball_one h1 (hσ2 b hb))
    rwa [add_sub_cancel] at this
  have hinj : Set.InjOn σ (B : Set F) := by
    intro b hb b' hb' he
    have hb0 : b ∈ B := hb
    have hb0' : b' ∈ B := hb'
    have e1 := sub_mem (hσ2 b hb0) (hσ2 b' hb0')
    rw [he] at e1
    have e2 := mul_mem (unit_inv_int hu) e1
    have e3 : ((u⁻¹ : Fˣ) : F) * (((ϖ⁻¹ : Fˣ) : F) * (c + u * b - σ b') -
        ((ϖ⁻¹ : Fˣ) : F) * (c + u * b' - σ b')) = ((ϖ⁻¹ : Fˣ) : F) * (b - b') := by
      have : ((u⁻¹ : Fˣ) : F) * (u : F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      linear_combination (((ϖ⁻¹ : Fˣ) : F) * (b - b')) * this
    rw [e3] at e2
    refine (h3 b (h2 b hb0)).unique ⟨hb0, ?_⟩ ⟨hb0', e2⟩
    simp
  have himg : B.image σ = B := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro t ht
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht
      exact hσ1 b hb
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ b ∈ B, G (c + u * b) = ∑ b ∈ B, G (σ b) := Finset.sum_congr rfl hGσ
    _ = ∑ t ∈ B.image σ, G t := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ B, G b := by rw [himg]

theorem ord_of_mem_filtration {v : Fˣ} {m : ℕ} (hv : v ∈ unitFiltrationUnits F m) : ord (v : F) = 0 :=
  mem_unitFiltrationUnits_zero_iff_ord.1 (unitFiltrationUnits_antitone (Nat.zero_le m) hv)

theorem sum_gU_eq_zero {n : ℕ} (hn : 1 ≤ n) {μ : Fˣ →* ℂˣ} (hk : unitFiltrationUnits F n ≤ μ.ker)
    {v : Fˣ} (hv : v ∈ unitFiltrationUnits F (n - 1)) (hv1 : μ v ≠ 1) {ϖ : Fˣ} {B : Finset F}
    (hB : Ad3.R.Reps ϖ B) {x y : F} (hx0 : x ≠ 0) (hx : ord x = (n : ℤ) - 1) :
    ∑ b ∈ B, gU μ (x * b + y) = 0 := by
  by_cases hall : ∀ b ∈ B, gU μ (x * b + y) = 0
  · exact Finset.sum_eq_zero hall
  push Not at hall
  obtain ⟨b₀, hb₀, hne⟩ := hall
  obtain ⟨hy0, hy1⟩ := gU_ne hne
  set y₀ := x * b₀ + y with hy₀
  have hvo : ord (v : F) = 0 := ord_of_mem_filtration hv
  have hbI : b₀ ∈ 𝒪[F] := hB.2.1 b₀ hb₀
  have hxb : x ∈ valBall F ((n : ℤ) - 1) := by rw [← hx]; exact mem_valBall_ord
  have hxi : x⁻¹ ∈ valBall F (-((n : ℤ) - 1)) := by
    rw [mem_valBall_iff_le_ord (inv_ne_zero hx0), ord_inv hx0, hx]
  have hv2 : (v : F) - 1 ∈ valBall F ((n : ℤ) - 1) := by
    have := unitFiltration_sub_one_mem_valBall hv
    have e : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rwa [e] at this
  have hy2 : y₀ ∈ valBall F 0 := by rw [mem_valBall_iff_le_ord hy0, hy1]
  set e := ((v : F) - 1) * y₀ * x⁻¹ with he
  have heI : e ∈ 𝒪[F] := by
    have := mul_mem_valBall (mul_mem_valBall hv2 hy2) hxi
    rw [← mem_valBall_zero_iff]
    simpa [he] using this
  set c := b₀ + e - v * b₀ with hc
  have hcI : c ∈ 𝒪[F] := sub_mem (add_mem hbI heI) (mul_mem (unit_int hvo) hbI)
  have hG : ∀ t, ∀ s ∈ valBall F 1, (fun t => gU μ (x * t + y)) (t + s) = (fun t => gU μ (x * t + y)) t := by
    intro t s hs
    have h1 : x * s ∈ valBall F (n : ℤ) := by
      simpa using mul_mem_valBall hxb hs
    have := gU_add hn hk (x * t + y) h1
    simp only []
    rw [← this]
    congr 1
    ring
  have key := sum_affine hB hvo hcI (fun t => gU μ (x * t + y)) hG
  have hmul : ∀ b ∈ B, gU μ (x * (c + v * b) + y) = ((μ v : ℂˣ) : ℂ) * gU μ (x * b + y) := by
    intro b _
    rw [← gU_mul μ v hvo]
    congr 1
    have : x * e = ((v : F) - 1) * y₀ := by
      rw [he]
      field_simp
    rw [hc, hy₀] at *
    linear_combination this
  simp only [Finset.sum_congr rfl hmul, ← Finset.mul_sum] at key
  refine eq_zero_of_eq_mul_of_ne_one (a := ((μ v : ℂˣ) : ℂ)) (fun h => hv1 (Units.ext h)) key.symm

theorem upm_0 (ϖ : Fˣ) (b : F) (r : Fin 2 → F) :
    (r ᵥ* ((Ad3.R.upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 0 = r 0 * ϖ := by
  simp [Ad3.R.upm, uni2, dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

theorem upm_1 (ϖ : Fˣ) (b : F) (r : Fin 2 → F) :
    (r ᵥ* ((Ad3.R.upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 = r 0 * b + r 1 := by
  simp [Ad3.R.upm, uni2, dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

theorem test_vector_hecke_sum {n : ℕ} (hn : 1 ≤ n) {μ : Fˣ →* ℂˣ} (hk : unitFiltrationUnits F n ≤ μ.ker)
    {v : Fˣ} (hv : v ∈ unitFiltrationUnits F (n - 1)) (hv1 : μ v ≠ 1) {ϖ : Fˣ} {B : Finset F}
    (hB : Ad3.R.Reps ϖ B) (r : Fin 2 → F) :
    ∑ b ∈ B, phi0 n μ (r ᵥ* ((Ad3.R.upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (B.card : ℂ) * phi0 n μ r := by
  simp only [phi0, Ad3.SchwartzSpaceL2.pt, upm_0, upm_1]
  rw [← Finset.mul_sum]
  have hϖ : (ϖ : F) ∈ valBall F 1 := by rw [mem_valBall_iff_le_ord ϖ.ne_zero, hB.1]
  by_cases h0 : r 0 ∈ valBall F (n : ℤ)
  · have h1 : r 0 * ϖ ∈ valBall F (n : ℤ) := by
      have := mul_mem_valBall h0 hϖ
      exact valBall_antitone (by omega) this
    rw [fB_of_mem h1, fB_of_mem h0, one_mul, one_mul]
    have : ∀ b ∈ B, gU μ (r 0 * b + r 1) = gU μ (r 1) := by
      intro b hb
      have h2 : r 0 * b ∈ valBall F (n : ℤ) := by
        simpa using mul_mem_valBall h0 (int_ball (hB.2.1 b hb))
      rw [add_comm]
      exact gU_add hn hk _ h2
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  · rw [fB_of_notMem h0, zero_mul, mul_zero]
    by_cases h1 : r 0 * ϖ ∈ valBall F (n : ℤ)
    · have hr0 : r 0 ≠ 0 := by
        intro h
        exact h0 (h ▸ zero_mem _)
      have h2 : ord (r 0) = (n : ℤ) - 1 := by
        rw [mem_valBall_iff_le_ord (mul_ne_zero hr0 ϖ.ne_zero), ord_mul hr0 ϖ.ne_zero, hB.1] at h1
        rw [mem_valBall_iff_le_ord hr0] at h0
        omega
      rw [sum_gU_eq_zero hn hk hv hv1 hB hr0 h2, mul_zero]
    · rw [fB_of_notMem h1, zero_mul]

variable [MeasurableSpace F] [BorelSpace F]

theorem mp_unit {u : Fˣ} (hu : ord (u : F) = 0) (s : ℂ) : mp u s = 1 := by
  simp [mp, modulus_eq_one_iff.2 ⟨u.ne_zero, hu⟩]

theorem mp_half {ϖ : Fˣ} (h : ord (ϖ : F) = 1) :
    mp ϖ (1 / 2) * (residueCard F : ℂ) = ((Real.sqrt (residueCard F) : ℝ) : ℂ) := by
  have hq : (0 : ℝ) < residueCard F := residueCard_pos_real
  have e : ((modulus (ϖ : F) : NNReal) : ℝ) = (residueCard F : ℝ)⁻¹ := by
    rw [modulus_of_ne_zero ϖ.ne_zero, h]
    simp
  have e2 : ((((residueCard F : ℝ)⁻¹ : ℝ)) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt ((residueCard F : ℝ)⁻¹) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  unfold mp
  rw [e, e2, Real.sqrt_inv]
  have hs : Real.sqrt (residueCard F) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hs' : ((Real.sqrt (residueCard F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have h2 : (residueCard F : ℂ) = ((Real.sqrt (residueCard F) : ℝ) : ℂ) * ((Real.sqrt (residueCard F) : ℝ) : ℂ) := by
    have := Real.mul_self_sqrt hq.le
    exact_mod_cast this.symm
  rw [h2]
  push_cast
  field_simp

theorem whittaker_finite_sum {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {ι : Type} (s : Finset ι) (f : ι → (Fin 2 → F) → ℂ)
    (hf : ∀ i ∈ s, f i ∈ GodementSectionLocal.schwartzBruhat2 F) (g : GL (Fin 2) F) :
    W2 ψ μ₁ μ₂ (∑ i ∈ s, f i) g = ∑ i ∈ s, W2 ψ μ₁ μ₂ (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W2]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ i ∈ s, f i ∈ GodementSectionLocal.schwartzBruhat2 F :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 : ∑ i ∈ s, f i ∈ GodementSectionLocal.schwartzBruhat2 F := Submodule.sum_mem _ h2
    rw [(GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ h1 _ h3).1, Pi.add_apply, ih h2]

theorem det_upm (ϖ : Fˣ) (b : F) : GeneralLinearGroup.det (Ad3.R.upm ϖ b) = ϖ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp [Ad3.R.upm, uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem whittaker_test_vector_newform_type {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) (hu : IsUnramifiedChar μ₂) (hn : 1 ≤ quasiCharConductor μ₁)
    (hcard : ∀ (ϖ : Fˣ) (B : Finset F), Ad3.R.Reps ϖ B → B.card = residueCard F) :
    Ad3.R.TypeU (μ₁ * μ₂) (quasiCharConductor μ₁)
      ((Real.sqrt (residueCard F) : ℝ) * ((μ₂ (unifUnit F) : ℂˣ) : ℂ))
      (W2 ψ μ₁ μ₂ (phi0 (quasiCharConductor μ₁) μ₁)) := by
  set n := quasiCharConductor μ₁ with hndef
  have hk : unitFiltrationUnits F n ≤ μ₁.ker := unitFiltrationUnits_quasiCharConductor_le_ker h₁.1
  have hφ := test_vector_mem_schwartz_bruhat hn hk
  have hnu : ¬ IsUnramifiedChar μ₁ := fun h => by
    have := (quasiCharConductor_eq_zero_iff h₁.1).2 h
    omega
  obtain ⟨v, hv, hv1⟩ := exists_apply_ne_one_of_not_isUnramified h₁.1 hnu
  refine ⟨fun x d hxd g => ?_, fun ϖ B hB g => ?_⟩
  · have hc := lower_left_entry_mem_ball hxd
    have e : Ad3.SchwartzSpaceL2.rt (phi0 n μ₁) x = ((μ₁ d : ℂˣ) : ℂ) • phi0 n μ₁ :=
      funext fun r => test_vector_congruence_equivariance hn hk hxd.1 hc hxd.2.2 r
    have hdet := GodementSectionLocal.ord_det_eq_zero hxd.1
    have hdo : ord (d : F) = 0 := by
      rw [hxd.2.2]
      exact (diag_unit hxd.1 (valBall_antitone (by omega) hc)).2.2.2
    rw [GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula, e,
      (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ hφ _ hφ).2, Pi.smul_apply, smul_eq_mul,
      isUnramifiedChar_iff.1 hu _ hdet, mp_unit hdet, MonoidHom.mul_apply,
      isUnramifiedChar_iff.1 hu _ hdo]
    simp
  · have e1 : ∀ b ∈ B, W2 ψ μ₁ μ₂ (phi0 n μ₁) (g * Ad3.R.upm ϖ b) =
        (((μ₂ ϖ : ℂˣ) : ℂ) * mp ϖ (1 / 2)) * W2 ψ μ₁ μ₂ (Ad3.SchwartzSpaceL2.rt (phi0 n μ₁) (Ad3.R.upm ϖ b)) g := by
      intro b _
      rw [GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula, det_upm]
    have e2 : ∑ b ∈ B, Ad3.SchwartzSpaceL2.rt (phi0 n μ₁) (Ad3.R.upm ϖ b) = (residueCard F : ℂ) • phi0 n μ₁ := by
      funext r
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hcard ϖ B hB]
      exact test_vector_hecke_sum hn hk hv hv1 hB r
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum,
      ← whittaker_finite_sum hψ h₁ h₂ B _ (fun b _ => GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hφ _) g, e2,
      (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ hφ _ hφ).2, Pi.smul_apply, smul_eq_mul,
      quasiChar_apply_eq_of_isUnramified hu hB.1, ← mp_half hB.1]
    ring

def Gt (ψ : AddChar F Circle) (μ : Fˣ →* ℂˣ) : F → ℂ := localFourier (selfDualMeasure ψ) ψ (gU μ)

theorem Gt_mul (ψ : AddChar F Circle) (μ : Fˣ →* ℂˣ) {u : Fˣ} (hu : ord (u : F) = 0) (t : F) :
    ((μ u : ℂˣ) : ℂ) * Gt ψ μ ((u : F) * t) = Gt ψ μ t := by
  have h := GlobalTheory.CompanionTheory.WhittakerTorus.integral_comp_unit_mul (selfDualMeasure ψ) u
    (fun z => gU μ z * (ψ (z * t) : ℂ))
  rw [modulus_eq_one_iff.2 ⟨u.ne_zero, hu⟩] at h
  simp only [NNReal.coe_one, Complex.ofReal_one, inv_one, one_mul] at h
  unfold Gt localFourier
  rw [← integral_const_mul, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [gU_mul μ u hu, show y * ((u : F) * t) = (u : F) * y * t by ring]
  ring

theorem Gt_add {ψ : AddChar F Circle} (hψ : IsStd ψ) (μ : Fˣ →* ℂˣ) (y : F) {s : F}
    (hs : s ∈ valBall F 0) : Gt ψ μ (y + s) = Gt ψ μ y := by
  refine localFourier_add_eq (selfDualMeasure ψ) hψ.1 hψ.2.1 (M := 0) (fun x hx => ?_) y ?_
  · have h5 := gU_ne hx
    rw [mem_valBall_iff_le_ord h5.1, h5.2]
  · rw [hψ.2.2]
    simpa using hs

theorem Gt_out {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n)
    (hk : unitFiltrationUnits F n ≤ μ.ker) {y : F} (hy : y ∉ valBall F (-(n : ℤ))) :
    Gt ψ μ y = 0 := by
  refine localFourier_eq_zero_of_notMem (selfDualMeasure ψ) hψ.1 hψ.2.1 (N := (n : ℤ))
    (fun x h hh => gU_add hn hk x hh) ?_
  rw [hψ.2.2]
  simpa using hy

theorem Gt_in {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n)
    {v : Fˣ} (hv : v ∈ unitFiltrationUnits F (n - 1)) (hv1 : μ v ≠ 1) {y : F}
    (hy : y ∈ valBall F (1 - (n : ℤ))) : Gt ψ μ y = 0 := by
  have hvo : ord (v : F) = 0 := ord_of_mem_filtration hv
  have hv2 : (v : F) - 1 ∈ valBall F ((n : ℤ) - 1) := by
    have := unitFiltration_sub_one_mem_valBall hv
    have e : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rwa [e] at this
  have hs : y * ((v : F) - 1) ∈ valBall F 0 := by
    simpa using mul_mem_valBall hy hv2
  have e : (v : F) * y = y + y * ((v : F) - 1) := by ring
  have h1 : Gt ψ μ ((v : F) * y) = Gt ψ μ y := by
    rw [e]
    exact Gt_add hψ μ y hs
  have m := Gt_mul ψ μ hvo y
  rw [h1] at m
  exact eq_zero_of_eq_mul_of_ne_one (fun h => hv1 (Units.ext h)) m.symm

theorem exists_Gt {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ : Fˣ →* ℂˣ} {n : ℕ} (hn : 1 ≤ n)
    (hk : unitFiltrationUnits F n ≤ μ.ker) : ∃ t, Gt ψ μ t ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : Gt ψ μ = 0 := funext h
  have h1 := localFourier_localFourier_selfDual hψ.1 hψ.2.1 (gU_mem hn hk) (-1 : F)
  change localFourier (selfDualMeasure ψ) ψ (Gt ψ μ) (-1) = _ at h1
  rw [h0, neg_neg] at h1
  have g1 : gU μ (1 : F) = 1 := by
    have := gU_unit μ 1 (by simp [ord_one])
    simpa using this
  rw [g1] at h1
  simp [localFourier] at h1

theorem ord_neg' {x : F} (hx : x ≠ 0) : ord (-x) = ord x := by
  have h1 : ord ((-1 : F) * (-1)) = ord (-1 : F) + ord (-1 : F) :=
    ord_mul (by simp) (by simp)
  have h2 : (-1 : F) * (-1) = 1 := by ring
  rw [h2, ord_one] at h1
  have h3 : ord ((-1 : F) * x) = ord (-1 : F) + ord x := ord_mul (by simp) hx
  have h4 : (-1 : F) * x = -x := by ring
  rw [h4] at h3
  omega

theorem whittaker_test_vector_ne_zero {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) (hu : IsUnramifiedChar μ₂) (hn : 1 ≤ quasiCharConductor μ₁) :
    W2 ψ μ₁ μ₂ (phi0 (quasiCharConductor μ₁) μ₁) 1 ≠ 0 := by
  set n := quasiCharConductor μ₁ with hndef
  have hk : unitFiltrationUnits F n ≤ μ₁.ker := unitFiltrationUnits_quasiCharConductor_le_ker h₁.1
  have hnu : ¬ IsUnramifiedChar μ₁ := fun h => by
    have := (quasiCharConductor_eq_zero_iff h₁.1).2 h
    omega
  obtain ⟨v, hv, hv1⟩ := exists_apply_ne_one_of_not_isUnramified h₁.1 hnu
  obtain ⟨t₀, ht₀⟩ := exists_Gt hψ hn hk
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    exact ht₀ (Gt_in hψ hn hv hv1 (zero_mem _))
  have hord : ord t₀ = -(n : ℤ) := by
    have h1 : t₀ ∈ valBall F (-(n : ℤ)) := by
      by_contra h
      exact ht₀ (Gt_out hψ hn hk h)
    have h2 : t₀ ∉ valBall F (1 - (n : ℤ)) := fun h => ht₀ (Gt_in hψ hn hv hv1 h)
    rw [mem_valBall_iff_le_ord ht0] at h1 h2
    omega
  have hS := GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ μ₁ μ₂ h₁ h₂ (fB n) (fB_mem n) (gU μ₁)
    (gU_mem hn hk) 1
  have d1 : dg2 (1 : Fˣ) (1 : Fˣ) = (1 : GL (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  rw [d1] at hS
  change W2 ψ μ₁ μ₂ (phi0 n μ₁) 1 = _ at hS
  rw [hS, map_one, Units.val_one, one_mul, mp_unit (by simp [ord_one]), one_mul]
  let h₀ : Fˣ := -(Units.mk0 t₀ ht0)⁻¹
  have hh₀ : -(((h₀⁻¹ : Fˣ)) : F) = t₀ := by
    simp [h₀]
  have hoh₀ : ord (h₀ : F) = n := by
    have : (h₀ : F) = -t₀⁻¹ := by simp [h₀]
    rw [this, ord_neg' (inv_ne_zero ht0), ord_inv ht0, hord]
    simp
  set I : Fˣ → ℂ := fun h => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * fB n ((h : F) * ((1 : Fˣ) : F)) *
    localFourier (selfDualMeasure ψ) ψ (gU μ₁) (-((h⁻¹ : Fˣ) : F)) with hI
  have hshell : ∀ h : Fˣ, ord (h : F) = n → fB n ((h : F) * ((1 : Fˣ) : F)) = 1 := by
    intro h hh
    refine fB_of_mem ?_
    rw [Units.val_one, mul_one, mem_valBall_iff_le_ord h.ne_zero, hh]
  have hind : I = (ordShell F (n : ℤ)).indicator fun _ => I h₀ := by
    funext h
    by_cases hh : ord (h : F) = n
    · rw [Set.indicator_of_mem (show h ∈ ordShell F (n : ℤ) from hh)]
      obtain ⟨u, e1⟩ : ∃ u : Fˣ, h = h₀ * u := ⟨h₀⁻¹ * h, by rw [mul_inv_cancel_left]⟩
      have huo : ord (u : F) = 0 := by
        rw [e1, ord_units_mul, hoh₀] at hh
        omega
      subst e1
      have huo' : ord ((u⁻¹ : Fˣ) : F) = 0 := by rw [ord_units_inv, huo]; rfl
      have e2 : -(((h₀ * u)⁻¹ : Fˣ) : F) = ((u⁻¹ : Fˣ) : F) * (-((h₀⁻¹ : Fˣ) : F)) := by
        rw [_root_.mul_inv_rev, Units.val_mul]
        ring
      have m := Gt_mul ψ μ₁ huo' (-((h₀⁻¹ : Fˣ) : F))
      rw [← e2] at m
      have hm : ((μ₁ u : ℂˣ) : ℂ) * ((μ₁ u⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      have m2 : Gt ψ μ₁ (-(((h₀ * u)⁻¹ : Fˣ) : F)) = ((μ₁ u : ℂˣ) : ℂ) * Gt ψ μ₁ (-((h₀⁻¹ : Fˣ) : F)) := by
        rw [← m, ← mul_assoc, hm, one_mul]
      have hμ2 := isUnramifiedChar_iff.1 hu _ huo
      change _ * _ * Gt ψ μ₁ _ = _ * _ * Gt ψ μ₁ _
      rw [m2, hshell _ hh, hshell h₀ hoh₀]
      have e3 : (((μ₁ (h₀ * u))⁻¹ * μ₂ (h₀ * u) : ℂˣ) : ℂ) * ((μ₁ u : ℂˣ) : ℂ) = (((μ₁ h₀)⁻¹ * μ₂ h₀ : ℂˣ) : ℂ) := by
        rw [← Units.val_mul]
        congr 1
        rw [map_mul, map_mul, hμ2, mul_one, _root_.mul_inv_rev, mul_right_comm, mul_comm (μ₁ u)⁻¹,
          inv_mul_cancel_right]
      rw [← e3]
      ring
    · rw [Set.indicator_of_notMem (show h ∉ ordShell F (n : ℤ) from hh)]
      rcases lt_or_gt_of_ne hh with hlt | hgt
      · have : fB n ((h : F) * ((1 : Fˣ) : F)) = 0 := by
          refine fB_of_notMem ?_
          rw [Units.val_one, mul_one, mem_valBall_iff_le_ord h.ne_zero]
          omega
        change (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * fB n ((h : F) * ((1 : Fˣ) : F)) * _ = 0
        rw [this]
        simp
      · have : Gt ψ μ₁ (-((h⁻¹ : Fˣ) : F)) = 0 := by
          refine Gt_out hψ hn hk ?_
          have h1 : ((h⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
          rw [mem_valBall_iff_le_ord (neg_ne_zero.2 h1), ord_neg' h1, ord_units_inv]
          omega
        change _ * _ * Gt ψ μ₁ _ = _
        rw [this, mul_zero]
  rw [hind]
  rw [integral_indicator_const _ (measurableSet_ordShell _), measureReal_def, multHaar_ordShell]
  simp only [ENNReal.toReal_one, one_smul]
  change _ * _ * Gt ψ μ₁ _ ≠ 0
  rw [hshell h₀ hoh₀, hh₀, mul_one]
  exact mul_ne_zero (Units.ne_zero _) ht₀

theorem main : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M1 := by
  intro _ hC F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ hu hn
  have hk : unitFiltrationUnits F (quasiCharConductor μ₁) ≤ μ₁.ker :=
    unitFiltrationUnits_quasiCharConductor_le_ker h₁.1
  have hφ := test_vector_mem_schwartz_bruhat hn hk
  have hne := whittaker_test_vector_ne_zero hψ h₁ h₂ hu hn
  have hcard := (hC F ψ hψ).2.1
  have hlin := (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ hφ _ hφ).2
  set c := (W2 ψ μ₁ μ₂ (phi0 (quasiCharConductor μ₁) μ₁) 1)⁻¹ with hc
  refine ⟨c • phi0 (quasiCharConductor μ₁) μ₁, Submodule.smul_mem _ c hφ, ?_, ?_⟩
  · rw [hlin, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hne
  · obtain ⟨t1, t2⟩ := whittaker_test_vector_newform_type hψ h₁ h₂ hu hn hcard
    rw [hlin]
    refine ⟨fun x d hxd g => ?_, fun ϖ B hB g => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [t1 x d hxd g]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, t2 ϖ B hB g]
      ring

end GlobalTheory.CompanionTheory.RankinTestVector
