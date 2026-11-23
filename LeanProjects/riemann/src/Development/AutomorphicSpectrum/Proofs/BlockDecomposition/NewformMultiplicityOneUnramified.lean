import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SphericalVector

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_O_iff {z : F} (hz : z ≠ 0) : z ∈ 𝒪[F] ↔ 0 ≤ ord z := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hz]

open scoped Classical in
theorem integral_lattice_indicator_apply (v : Fin 2 → F) :
    (ind0 v : ℂ) = if v 0 ∈ 𝒪[F] ∧ v 1 ∈ 𝒪[F] then 1 else 0 := by
  simp [ind0, Set.indicator, Fin.forall_fin_two]

theorem integral_lattice_indicator_mem_schwartz_bruhat : (ind0 : (Fin 2 → F) → ℂ) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  have : (ind0 : (Fin 2 → F) → ℂ) = GodementSectionLocal.boxInd F 0 := by
    unfold ind0 GodementSectionLocal.boxInd
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, GodementSectionLocal.mem_box,
      mem_valBall_zero_iff]
  rw [this]
  exact GodementSectionLocal.boxInd_mem 0

theorem vec_dg (a d : Fˣ) (r : Fin 2 → F) :
    r ᵥ* ((dg2 a d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ![r 0 * a, r 1 * d] := by
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vec_upm (ϖ : Fˣ) (b : F) (r : Fin 2 → F) :
    r ᵥ* ((upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ![r 0 * ϖ, r 0 * b + r 1] := by
  ext i
  fin_cases i <;>
    simp [upm, uni2, dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

theorem det_dg (a d : Fˣ) : GeneralLinearGroup.det (dg2 a d : GL (Fin 2) F) = a * d := by
  ext
  simp [dg2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem det_upm (ϖ : Fˣ) (b : F) : GeneralLinearGroup.det (upm ϖ b) = ϖ := by
  ext
  simp [upm, uni2, dg2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_comm (a : Fˣ) (g : GL (Fin 2) F) : dg2 a a * g = g * dg2 a a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem vec_mem {A : Matrix (Fin 2) (Fin 2) F} (hA : ∀ i j, A i j ∈ 𝒪[F]) {r : Fin 2 → F}
    (h0 : r 0 ∈ 𝒪[F]) (h1 : r 1 ∈ 𝒪[F]) (j : Fin 2) : (r ᵥ* A) j ∈ 𝒪[F] := by
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem h0 (hA _ _)) (mul_mem h1 (hA _ _))

theorem ord_det_of_mem {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2) :
    ord ((GeneralLinearGroup.det x : Fˣ) : F) = 0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  have key : ∀ y : GL (Fin 2) F, (∀ i j, y i j ∈ 𝒪[F]) →
      ((GeneralLinearGroup.det y : Fˣ) : F) ∈ 𝒪[F] := by
    intro y hy
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hy _ _) (hy _ _)) (mul_mem (hy _ _) (hy _ _))
  have a := (mem_O_iff (Units.ne_zero _)).1 (key x h1)
  have b := (mem_O_iff (Units.ne_zero _)).1 (key x⁻¹ h2)
  rw [map_inv, ord_units_inv] at b
  omega

theorem right_translate_lattice_indicator_integral {x : GL (Fin 2) F} (hx : x ∈ GLnLocal.integralGL F 2) :
    rt (ind0 : (Fin 2 → F) → ℂ) x = ind0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hx
  funext r
  have back : r = (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) ᵥ*
      ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have iff : ((r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) 0 ∈ 𝒪[F] ∧
      (r ᵥ* (x : Matrix (Fin 2) (Fin 2) F)) 1 ∈ 𝒪[F]) ↔ (r 0 ∈ 𝒪[F] ∧ r 1 ∈ 𝒪[F]) := by
    constructor
    · rintro ⟨a, b⟩
      rw [back]
      exact ⟨vec_mem h2 a b 0, vec_mem h2 a b 1⟩
    · rintro ⟨a, b⟩
      exact ⟨vec_mem h1 a b 0, vec_mem h1 a b 1⟩
  simp only [rt, integral_lattice_indicator_apply]
  by_cases h : r 0 ∈ 𝒪[F] ∧ r 1 ∈ 𝒪[F]
  · rw [if_pos (iff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (iff.1 h')), if_neg h]

open scoped Classical in

theorem spherical_vector_hecke_relation {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) (r : Fin 2 → F) :
    ∑ b ∈ B, (ind0 (r ᵥ* ((upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : ℂ) +
        ind0 (r ᵥ* ((dg2 1 ϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      (B.card : ℂ) * ind0 r + ind0 (r ᵥ* ((dg2 ϖ ϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  obtain ⟨hord, hB, hu⟩ := hR
  have hp0 : (ϖ : F) ≠ 0 := ϖ.ne_zero
  have hpO : (ϖ : F) ∈ 𝒪[F] := (mem_O_iff hp0).2 (by omega)
  have t1 : ∀ b, (ind0 (r ᵥ* ((upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : ℂ) =
      if r 0 * ϖ ∈ 𝒪[F] ∧ r 0 * b + r 1 ∈ 𝒪[F] then 1 else 0 := by
    intro b
    rw [vec_upm, integral_lattice_indicator_apply]
    simp
  have t2 : (ind0 (r ᵥ* ((dg2 1 ϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : ℂ) =
      if r 0 ∈ 𝒪[F] ∧ r 1 * ϖ ∈ 𝒪[F] then 1 else 0 := by
    rw [vec_dg, integral_lattice_indicator_apply]
    simp
  have t3 : (ind0 (r ᵥ* ((dg2 ϖ ϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : ℂ) =
      if r 0 * ϖ ∈ 𝒪[F] ∧ r 1 * ϖ ∈ 𝒪[F] then 1 else 0 := by
    rw [vec_dg, integral_lattice_indicator_apply]
    simp
  simp only [t1, t2, t3, integral_lattice_indicator_apply r]
  generalize r 0 = x
  generalize r 1 = y
  by_cases hx : x ∈ 𝒪[F]
  · by_cases hy : y ∈ 𝒪[F]
    · have a : ∀ b ∈ B, (if x * ϖ ∈ 𝒪[F] ∧ x * b + y ∈ 𝒪[F] then (1 : ℂ) else 0) = 1 :=
        fun b hb => if_pos ⟨mul_mem hx hpO, add_mem (mul_mem hx (hB b hb)) hy⟩
      rw [Finset.sum_congr rfl a, if_pos ⟨hx, mul_mem hy hpO⟩, if_pos ⟨hx, hy⟩,
        if_pos ⟨mul_mem hx hpO, mul_mem hy hpO⟩]
      simp
    · have a : ∀ b ∈ B, (if x * ϖ ∈ 𝒪[F] ∧ x * b + y ∈ 𝒪[F] then (1 : ℂ) else 0) = 0 := by
        intro b hb
        refine if_neg fun h => hy ?_
        have := sub_mem h.2 (mul_mem hx (hB b hb))
        simpa using this
      rw [Finset.sum_congr rfl a, if_neg (show ¬(x ∈ 𝒪[F] ∧ y ∈ 𝒪[F]) from fun h => hy h.2)]
      simp [hx, mul_mem hx hpO]
  · rw [if_neg (fun h => hx h.1), if_neg (fun h => hx h.1)]
    by_cases hxp : x * ϖ ∈ 𝒪[F]
    · by_cases hyp : y * ϖ ∈ 𝒪[F]
      · have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem _)
        have o1 := (mem_O_iff (mul_ne_zero hx0 hp0)).1 hxp
        have o2 : ¬ 0 ≤ ord x := fun h => hx ((mem_O_iff hx0).2 h)
        rw [ord_mul hx0 hp0, hord] at o1
        have hc0 : x * ϖ ≠ 0 := mul_ne_zero hx0 hp0
        have hinv : (x * ϖ)⁻¹ ∈ 𝒪[F] := by
          refine (mem_O_iff (inv_ne_zero hc0)).2 ?_
          rw [ord_inv hc0, ord_mul hx0 hp0, hord]
          omega
        set t : F := -(y * ϖ) * (x * ϖ)⁻¹ with ht
        have htO : t ∈ 𝒪[F] := mul_mem (neg_mem hyp) hinv
        have hpinv : ((ϖ⁻¹ : Fˣ) : F) = (ϖ : F)⁻¹ := Units.val_inv_eq_inv_val ϖ
        have equiv : ∀ b, (x * b + y ∈ 𝒪[F] ↔ ((ϖ⁻¹ : Fˣ) : F) * (t - b) ∈ 𝒪[F]) := by
          intro b
          have e1 : x * b + y = -(x * ϖ) * (((ϖ⁻¹ : Fˣ) : F) * (t - b)) := by
            rw [hpinv, ht]
            field_simp
            ring
          have e2 : ((ϖ⁻¹ : Fˣ) : F) * (t - b) = -(x * ϖ)⁻¹ * (x * b + y) := by
            rw [e1]
            field_simp
          constructor
          · intro h
            rw [e2]
            exact mul_mem (neg_mem hinv) h
          · intro h
            rw [e1]
            exact mul_mem (neg_mem hxp) h
        obtain ⟨b₀, ⟨hb₀, hb₀'⟩, huniq⟩ := hu t htO
        rw [Finset.sum_eq_single_of_mem b₀ hb₀, if_pos ⟨hxp, (equiv b₀).2 hb₀'⟩,
          if_pos ⟨hxp, hyp⟩]
        · simp
        · intro b hb hne
          exact if_neg fun h => hne (huniq b ⟨hb, (equiv b).1 h.2⟩)
      · have a : ∀ b ∈ B, (if x * ϖ ∈ 𝒪[F] ∧ x * b + y ∈ 𝒪[F] then (1 : ℂ) else 0) = 0 := by
          intro b hb
          refine if_neg fun h => hyp ?_
          have e : y * ϖ = (x * b + y) * ϖ - (x * ϖ) * b := by ring
          rw [e]
          exact sub_mem (mul_mem h.2 hpO) (mul_mem hxp (hB b hb))
        rw [Finset.sum_congr rfl a, if_neg (fun h => hyp h.2)]
        simp
    · have a : ∀ b ∈ B, (if x * ϖ ∈ 𝒪[F] ∧ x * b + y ∈ 𝒪[F] then (1 : ℂ) else 0) = 0 :=
        fun b _ => if_neg fun h => hxp h.1
      rw [Finset.sum_congr rfl a, if_neg (fun h => hxp h.1)]
      simp

theorem mp_half_of_ord {ϖ : Fˣ} (h : ord (ϖ : F) = 1) :
    mp ϖ (1 / 2) = (((Real.sqrt (residueCard F) : ℝ) : ℂ))⁻¹ := by
  have hq : (0 : ℝ) < residueCard F := by exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have e : ((modulus (ϖ : F) : ℝ)) = ((residueCard F : ℝ))⁻¹ := by
    rw [modulus_of_ne_zero ϖ.ne_zero, h]
    simp
  have e2 := Complex.ofReal_cpow (inv_nonneg.2 hq.le) (1 / 2 : ℝ)
  unfold mp
  rw [e, Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.inv_rpow hq.le]
  rw [e2]
  push_cast
  rfl

variable [MeasurableSpace F] [BorelSpace F]

theorem whittaker_finite_sum {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {ι : Type} (s : Finset ι) (f : ι → (Fin 2 → F) → ℂ)
    (hf : ∀ i ∈ s, f i ∈ GodementSectionLocal.schwartzBruhat2 F) :
    W2 ψ μ₁ μ₂ (∑ i ∈ s, f i) = ∑ i ∈ s, W2 ψ μ₁ μ₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ 0 (zero_mem _) 0 (zero_mem _)).2 0
    simpa using this
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ∈ GodementSectionLocal.schwartzBruhat2 F :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ (hf a (Finset.mem_insert_self a s)) _
        (Submodule.sum_mem _ hs)).1, ih hs]

theorem inner_unit {ψ : AddChar F Circle} (hψ : IsStd ψ) {h : Fˣ} (hh : ord (h : F) = 0) :
    ∫ x, (ind0 ![(h : F), (h : F) * x] : ℂ) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ = 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have hO : (h : F) ∈ 𝒪[F] := (mem_O_iff h.ne_zero).2 hh.ge
  have pt : ∀ x : F, (ind0 ![(h : F), (h : F) * x] : ℂ) * (ψ (-x) : ℂ) =
      ((valBall F 0 : Set F)).indicator (fun _ => (1 : ℂ)) x := by
    intro x
    by_cases hx : x ∈ valBall F 0
    · have hxO : x ∈ 𝒪[F] := mem_valBall_zero_iff.1 hx
      have hψx : ψ (-x) = 1 := by
        have := isTrivialOn_addCharConductor hc h1
        rw [h0] at this
        exact this _ (neg_mem hx)
      rw [Set.indicator_of_mem (show x ∈ (valBall F 0 : Set F) from hx), integral_lattice_indicator_apply, hψx]
      simp [hO, mul_mem hO hxO]
    · have hxO : x ∉ 𝒪[F] := fun h' => hx (mem_valBall_zero_iff.2 h')
      have hx0 : x ≠ 0 := fun h' => hxO (h' ▸ zero_mem _)
      have : (h : F) * x ∉ 𝒪[F] := by
        intro h'
        have a := (mem_O_iff (mul_ne_zero h.ne_zero hx0)).1 h'
        rw [ord_mul h.ne_zero hx0, hh] at a
        exact hxO ((mem_O_iff hx0).2 (by omega))
      rw [Set.indicator_of_notMem (show x ∉ (valBall F 0 : Set F) from hx), integral_lattice_indicator_apply]
      simp [this]
  simp only [pt]
  rw [integral_indicator (measurableSet_valBall 0), setIntegral_const,
    selfDualMeasure_real_valBall_zero, h0]
  simp

theorem whittaker_spherical_at_identity {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ}
    (u₁ : IsUnramifiedChar μ₁) (u₂ : IsUnramifiedChar μ₂) : W2 ψ μ₁ μ₂ ind0 1 = 1 := by
  have hψ' := hψ
  obtain ⟨hc, h1, h0⟩ := hψ'
  obtain ⟨x₀, hx₀b, hx₀⟩ : ∃ x ∈ valBall F (-1), ψ x ≠ 1 := by
    have := not_isTrivialOn_addCharConductor_sub_one hc h1
    rw [h0] at this
    simpa [IsTrivialOn] using this
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  have hinv : ∀ x : Fin 2 → F, ∀ d ∈ GodementSectionLocal.box F 0,
      (ind0 (x + d) : ℂ) = ind0 x := by
    intro x d hd
    have d0 : d 0 ∈ 𝒪[F] := mem_valBall_zero_iff.1 (GodementSectionLocal.mem_box.1 hd 0)
    have d1 : d 1 ∈ 𝒪[F] := mem_valBall_zero_iff.1 (GodementSectionLocal.mem_box.1 hd 1)
    have e : ∀ (a b : F), b ∈ 𝒪[F] → (a + b ∈ 𝒪[F] ↔ a ∈ 𝒪[F]) := fun a b hb =>
      ⟨fun h => by simpa using sub_mem h hb, fun h => add_mem h hb⟩
    have a := e (x 0) _ d0
    have b := e (x 1) _ d1
    rw [integral_lattice_indicator_apply, integral_lattice_indicator_apply]
    simp only [Pi.add_apply]
    by_cases h : x 0 ∈ 𝒪[F] ∧ x 1 ∈ 𝒪[F]
    · rw [if_pos ⟨a.2 h.1, b.2 h.2⟩, if_pos h]
    · rw [if_neg (fun h' => h ⟨a.1 h'.1, b.1 h'.2⟩), if_neg h]
  have hsup : ∀ x : Fin 2 → F, (ind0 x : ℂ) ≠ 0 → x ∈ GodementSectionLocal.box F 0 := by
    intro x hx
    rw [integral_lattice_indicator_apply] at hx
    have : x 0 ∈ 𝒪[F] ∧ x 1 ∈ 𝒪[F] := by
      by_contra hn
      exact hx (if_neg hn)
    exact GodementSectionLocal.mem_box.2 fun i => by
      fin_cases i
      · exact mem_valBall_zero_iff.2 this.1
      · exact mem_valBall_zero_iff.2 this.2
  have hI : ∀ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, (ind0 (![(h : F), (h : F) * x] ᵥ* ((1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) : ℂ) *
        (ψ (-x) : ℂ) ∂selfDualMeasure ψ) = (ordShell F 0).indicator (fun _ => (1 : ℂ)) h := by
    intro h
    simp only [Units.val_one, Matrix.vecMul_one]
    rcases lt_trichotomy (ord (h : F)) 0 with hh | hh | hh
    · rw [GlobalTheory.CompanionTheory.WhitLin.inner_eq_zero_of_lt _ hsup h hh,
        Set.indicator_of_notMem (show h ∉ ordShell F 0 from fun h' => hh.ne h')]
      simp
    · have hu : h ∈ unitFiltrationUnits F 0 := mem_unitFiltrationUnits_zero_iff_ord.2 hh
      have a₁ : μ₁ h = 1 := u₁ hu
      have a₂ : μ₂ h = 1 := u₂ hu
      have hm : mp h 1 = 1 := by
        have : modulus (h : F) = 1 := modulus_eq_one_iff.2 ⟨h.ne_zero, hh⟩
        simp [mp, this]
      rw [inner_unit hψ hh, Set.indicator_of_mem (show h ∈ ordShell F 0 from hh), a₁, a₂, hm]
      simp
    · rw [GlobalTheory.CompanionTheory.WhitLin.inner_eq_zero _ hinv hx₀ h ?_,
        Set.indicator_of_notMem (show h ∉ ordShell F 0 from fun h' => hh.ne' h')]
      · simp
      · have := (mem_valBall_iff_le_ord hx₀0).1 hx₀b
        rw [mem_valBall_iff_le_ord (mul_ne_zero h.ne_zero hx₀0), ord_mul h.ne_zero hx₀0]
        omega
  unfold W2
  simp only [hI]
  rw [integral_indicator (measurableSet_ordShell 0), setIntegral_const]
  simp [measureReal_def, multHaar_ordShell, GlobalTheory.CompanionTheory.WhittakerCentral.mp_one_left]

theorem unr_eq {μ : Fˣ →* ℂˣ} (u : IsUnramifiedChar μ) {ϖ : Fˣ} (h : ord (ϖ : F) = 1) :
    μ ϖ = μ (unifUnit F) := by
  have hm : ϖ * (unifUnit F)⁻¹ ∈ unitFiltrationUnits F 0 := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_units_inv, ord_unifUnit, h]
    omega
  have h1 : μ (ϖ * (unifUnit F)⁻¹) = 1 := u hm
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem hecke_alg {s w D a b : ℂ} (hs : s ≠ 0) (hb : b ≠ 0)
    (hD : a * b * w = b * b * (s⁻¹ * s⁻¹) * D) :
    b * s⁻¹ * (s * s * w + D) = s * (a + b) * w := by
  have h2 : b * b * (s⁻¹ * s⁻¹) ≠ 0 := by simp [hs, hb]
  have hD' : D = a * b⁻¹ * (s * s) * w := by
    apply mul_left_cancel₀ h2
    rw [← hD]
    field_simp
  rw [hD']
  field_simp
  ring

theorem hecke {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) (u₁ : IsUnramifiedChar μ₁) (u₂ : IsUnramifiedChar μ₂)
    {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) (hq : B.card = residueCard F) (g : GL (Fin 2) F) :
    ∑ b ∈ B, W2 ψ μ₁ μ₂ ind0 (g * upm ϖ b) + W2 ψ μ₁ μ₂ ind0 (g * dg2 1 ϖ) =
      ((Real.sqrt (residueCard F) : ℝ) * (((μ₁ (unifUnit F) : ℂˣ) : ℂ) + ((μ₂ (unifUnit F) : ℂˣ) : ℂ))) *
        W2 ψ μ₁ μ₂ ind0 g := by
  have hsb := integral_lattice_indicator_mem_schwartz_bruhat (F := F)
  have hord := hR.1
  have hrt := fun k : GL (Fin 2) F => GlobalTheory.CompanionTheory.WhitLin.rt_mem hsb k
  have hlin := GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂
  have hS := whittaker_finite_sum hψ h₁ h₂ B (fun b => rt ind0 (upm ϖ b)) (fun b _ => hrt _)
  have hSm : (∑ b ∈ B, rt ind0 (upm ϖ b)) ∈ GodementSectionLocal.schwartzBruhat2 F :=
    Submodule.sum_mem _ fun b _ => hrt _
  have hfun : (∑ b ∈ B, rt ind0 (upm ϖ b)) + rt ind0 (dg2 1 ϖ) =
      ((B.card : ℂ) • (ind0 : (Fin 2 → F) → ℂ)) + rt ind0 (dg2 ϖ ϖ) := by
    funext r
    simpa [Finset.sum_apply, rt] using spherical_vector_hecke_relation hR r
  have e1 := congrFun (hlin _ hSm _ (hrt (dg2 1 ϖ))).1 g
  have e2 := congrFun (hlin ((B.card : ℂ) • ind0) (Submodule.smul_mem _ _ hsb) _ (hrt (dg2 ϖ ϖ))).1 g
  have e3 := congrFun ((hlin _ hsb _ hsb).2 (B.card : ℂ)) g
  rw [hfun, e2, Pi.add_apply, e3, Pi.add_apply, hS] at e1
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at e1
  have hcen : W2 ψ μ₁ μ₂ ind0 (g * dg2 ϖ ϖ) = ((μ₁ ϖ * μ₂ ϖ : ℂˣ) : ℂ) * W2 ψ μ₁ μ₂ ind0 g := by
    rw [← dg_comm]
    exact GlobalTheory.CompanionTheory.WhittakerCentral.whittaker_central_character_equivariance ψ μ₁ μ₂ ind0 ϖ g
  have hD := GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula ψ μ₁ μ₂ ind0 g (dg2 ϖ ϖ)
  rw [hcen, det_dg, map_mul, GlobalTheory.CompanionTheory.WhittakerCentral.mp_mul, mp_half_of_ord hord] at hD
  have hup : ∀ b ∈ B, W2 ψ μ₁ μ₂ ind0 (g * upm ϖ b) = ((μ₂ ϖ : ℂˣ) : ℂ) * mp ϖ (1 / 2) *
      W2 ψ μ₁ μ₂ (rt ind0 (upm ϖ b)) g := by
    intro b _
    rw [GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula, det_upm]
  have hdg : W2 ψ μ₁ μ₂ ind0 (g * dg2 1 ϖ) = ((μ₂ ϖ : ℂˣ) : ℂ) * mp ϖ (1 / 2) *
      W2 ψ μ₁ μ₂ (rt ind0 (dg2 1 ϖ)) g := by
    rw [GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula, det_dg, one_mul]
  rw [Finset.sum_congr rfl hup, ← Finset.mul_sum, hdg, ← mul_add, ← e1, mp_half_of_ord hord,
    ← unr_eq u₁ hord, ← unr_eq u₂ hord, hq]
  have hs0 : ((Real.sqrt (residueCard F) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < residueCard F := by exact_mod_cast zero_lt_one.trans one_lt_residueCard
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  have hsq : ((Real.sqrt (residueCard F) : ℝ) : ℂ) * ((Real.sqrt (residueCard F) : ℝ) : ℂ) =
      (residueCard F : ℂ) := by
    have : (0 : ℝ) ≤ residueCard F := Nat.cast_nonneg _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt this]
    simp
  have hB0 : ((μ₂ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [Units.val_mul] at hD
  rw [← hsq]
  exact hecke_alg hs0 hB0 hD

theorem m0 : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M0 := by
  intro _ hC F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ u₁ u₂
  obtain ⟨-, hcard, -⟩ := hC F ψ hψ
  refine ⟨integral_lattice_indicator_mem_schwartz_bruhat, whittaker_spherical_at_identity hψ u₁ u₂, fun x hx g => ?_, fun ϖ B hR g => ?_⟩
  · have hu : GeneralLinearGroup.det x ∈ unitFiltrationUnits F 0 :=
      mem_unitFiltrationUnits_zero_iff_ord.2 (ord_det_of_mem hx)
    have a₂ : μ₂ (GeneralLinearGroup.det x) = 1 := u₂ hu
    have hm : mp (GeneralLinearGroup.det x) (1 / 2) = 1 := by
      have : modulus ((GeneralLinearGroup.det x : Fˣ) : F) = 1 :=
        modulus_eq_one_iff.2 ⟨Units.ne_zero _, ord_det_of_mem hx⟩
      unfold mp
      rw [this]
      simp
    rw [GlobalTheory.CompanionTheory.WhittakerTrans.whittaker_right_translation_formula, a₂, hm, right_translate_lattice_indicator_integral hx]
    simp
  · exact hecke hψ h₁ h₂ u₁ u₂ hR (hcard ϖ B hR) g

end GlobalTheory.CompanionTheory.SphericalVector
