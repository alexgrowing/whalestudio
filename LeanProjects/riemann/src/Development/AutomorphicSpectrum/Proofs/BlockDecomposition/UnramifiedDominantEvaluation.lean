import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeGlTwoTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralValueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductLeftIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMatrixRowRepExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowRepsDistinctCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValuesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRowRepFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerUnipotentEquivariantHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTorusValueFormulaHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterUniformizerPowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetTorusPowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetRowRepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerZpowMemIntegersIffStatement

noncomputable section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom
open Ad3 Ad3.LFS

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

local notation "ϖ" => (GLnLocal.uniformizer F : F)

theorem mp_mul' (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simpa [mp, GodementSectionLocal.modPow] using GodementSectionLocal.modPow_mul (a : F) (b : F) s

theorem standard_character_trivial_integers {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  intro x hx
  have := ht x (mem_valBall_zero_iff.2 hx)
  simp [this]

def f1 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (k : GL (Fin 2) F) : ℂ :=
  s2 ψ ν (k * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ *
    mp (GeneralLinearGroup.det (k * (torusPow F 2 ![l 0, l 1])⁻¹)) (3 / 2) *
    inn ψ (Φ0 F) (k * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l)

theorem unramified_vector_left_invariant {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ)
    {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) (k : GL (Fin 2) F) :
    f1 ψ ν l (κ * k) = f1 ψ ν l k := by
  unfold f1
  rw [mul_assoc κ k, GlobalTheory.T.local_inner_product_left_integral F ψ κ hκ, map_mul GeneralLinearGroup.det κ, mp_mul',
    GlobalTheory.CompanionTheory.LFNe.mp_det_eq_one hκ, one_mul, mul_inv_rev (κ) _]
  congr 2
  exact sphericalWhittaker_mul_right (standard_character_trivial_integers hψ) _ _ ((integralGL F 2).inv_mem hκ)

theorem unramified_vector_support_integral (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (k : GL (Fin 2) F)
    (h : f1 ψ ν l k ≠ 0) : ∀ a b, (k : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F] := by
  by_contra hk
  apply h
  unfold f1
  rw [(GlobalTheory.T.local_inner_product_support F ψ (k * (torusPow F 2 ![l 0, l 1])⁻¹) l).1 (by simpa using hk), mul_zero]

abbrev V2 (ψ : AddChar F Circle) : ℝ := (vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]}

theorem unifUnit_zpow_val (z : ℤ) : ((uniformizerUnit F ^ z : Fˣ) : F) = ϖ ^ z := by
  simp [Units.val_zpow_eq_zpow_val]

theorem det_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    GeneralLinearGroup.det (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) =
      uniformizerUnit F ^ ((i : ℤ) + j - l 0 - l 1) := by
  rw [map_mul, map_inv, GlobalTheory.T.det_row_rep, GlobalTheory.T.det_torus_power, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← _root_.zpow_neg, ← _root_.zpow_add]
  congr 1
  ring

theorem inv_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ =
      uni2 (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) * torusPow F 2 ![l 0 - i, l 1 - j] := by
  rw [_root_.mul_inv_rev, inv_inv, GlobalTheory.T.torus_row_rep_factorization]

theorem row_A (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) (b : Fin 2) :
    (((torusPow F 2 ![l 2, l 2] * (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹))⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 b = if b = 1 then ϖ ^ (l 1 - j - l 2) else 0 := by
  rw [_root_.mul_inv_rev, inv_kd, mul_assoc, ← torusPow_neg, ← torusPow_add]
  have e : (![l 0 - i, l 1 - j] + -![l 2, l 2] : Fin 2 → ℤ) = ![l 0 - i - l 2, l 1 - j - l 2] := by
    ext t; fin_cases t <;> simp <;> ring
  rw [e, Units.val_mul, coe_torusPow]
  simp only [uni2]
  fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem inn_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    inn ψ (Φ0 F) (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l) =
      if (j : ℤ) ≤ l 1 - l 2 then
        sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) * ((V2 ψ : ℝ) : ℂ) else 0 := by
  set k := rowRep i j c with hk
  set d := torusPow F 2 ![l 0, l 1] with hd
  set A := torusPow F 2 ![l 2, l 2] * (k * d⁻¹) with hA
  have hint : ∀ a b, (((k * d⁻¹ * d : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F] := by
    intro a b
    rw [inv_mul_cancel_right, hk, coe_rowRep]
    have h0 := (GLnLocal.uniformizer F).2
    fin_cases a <;> fin_cases b <;> simp
    · exact pow_mem h0 _
    · exact digitSum_mem _ _
    · exact pow_mem h0 _
  rw [(GlobalTheory.T.local_inner_product_support F ψ (k * d⁻¹) l).2 hint]
  have hrow : (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) ↔ (j : ℤ) ≤ l 1 - l 2 := by
    rw [Fin.forall_fin_two, hA, hk, hd, row_A, row_A]
    simp only [zero_ne_one, if_false, if_true, Subring.zero_mem, true_and, GlobalTheory.T.uniformizer_zpow_mem_integers_iff']
    constructor <;> intro h <;> linarith
  split_ifs with hj
  · rw [GlobalTheory.T.lattice_character_integral_value F ψ hψ A (hrow.2 hj), GlobalTheory.T.lattice_volume_gl_two_translate F ψ hψ A]
    have hdet : GeneralLinearGroup.det A = uniformizerUnit F ^ (2 * l 2 + i + j - l 0 - l 1) := by
      rw [hA, map_mul, GlobalTheory.T.det_torus_power, det_kd, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← _root_.zpow_add]
      congr 1
      ring
    have hm := GlobalTheory.T.unramified_character_uniformizer_power F (2 * l 2 + i + j - l 0 - l 1) (-2)
    rw [← hdet] at hm
    have hm' : mp (GeneralLinearGroup.det A) (-1) = ((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ) : ℂ)⁻¹ := by
      simp [mp, Complex.cpow_neg_one]
    have e1 : (((-2 : ℤ) : ℂ) / 2) = -1 := by norm_num
    rw [e1, hm'] at hm
    push_cast
    rw [hm]
    congr 2
    ring
  · exact GlobalTheory.T.lattice_character_integral_zero F ψ hψ A (fun h => hj (hrow.1 h))

def Cc (ψ : AddChar F Circle) (l : Fin 3 → ℤ) (i j : ℕ) : ℂ :=
  sqrtQ F ^ (-(3 * ((i : ℤ) + j - l 0 - l 1))) * sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) *
    ((V2 ψ : ℝ) : ℂ)

theorem unramified_vector_rep_formula {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (c : Fin j → 𝓀[F]) :
    f1 ψ ν l (rowRep i j c) = if (j : ℤ) ≤ l 1 - l 2 then
      ((ψ (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) : Circle) : ℂ) *
        s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  unfold f1
  rw [inv_kd, GlobalTheory.T.whittaker_unipotent_equivariant_holds F ψ hψ, det_kd, inn_rep hψ]
  have hm := GlobalTheory.T.unramified_character_uniformizer_power F ((i : ℤ) + j - l 0 - l 1) 3
  have e : (((3 : ℤ) : ℂ) / 2) = 3 / 2 := by norm_num
  rw [e] at hm
  rw [hm]
  split_ifs
  · simp only [Cc]
    ring
  · simp

theorem unramified_vector_rep_support {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (c : Fin j → 𝓀[F]) (h : f1 ψ ν l (rowRep i j c) ≠ 0) :
    (j : ℤ) ≤ l 1 - l 2 ∧ l 1 - j ≤ l 0 - i := by
  rw [unramified_vector_rep_formula hψ] at h
  split_ifs at h with hj
  · refine ⟨hj, ?_⟩
    by_contra h2
    apply h
    rw [(GlobalTheory.T.whittaker_torus_value_formula_holds F ψ hψ ν _ _).2 (not_le.1 h2)]
    simp
  · exact absurd rfl h

theorem sum_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (hj : (j : ℤ) ≤ l 1 - l 2) :
    ∑ c : Fin j → 𝓀[F], f1 ψ ν l (rowRep i j c) = if (i : ℤ) ≤ l 0 - l 1 then
      (qF F : ℂ) ^ j * s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  simp_rw [unramified_vector_rep_formula hψ, if_pos hj]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  split_ifs with hi
  · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).1 (by linarith)]
  · by_cases h2 : l 1 - j ≤ l 0 - i
    · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).2 (by linarith) (by linarith)]
      simp
    · rw [(GlobalTheory.T.whittaker_torus_value_formula_holds F ψ hψ ν _ _).2 (not_le.1 h2)]
      simp

theorem sum_range_reindex (u v : ℤ) (huv : u ≤ v) (N : ℕ) (hN : (v - u + 1).toNat ≤ N) (g : ℕ → ℂ)
    (hg : ∀ i ∈ Finset.range N, i ∉ Finset.range (v - u + 1).toNat → g i = 0) :
    ∑ i ∈ Finset.range N, g i = ∑ a ∈ Finset.Icc u v, g (v - a).toNat := by
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hN) hg]
  refine Finset.sum_nbij' (fun i : ℕ => v - i) (fun a => (v - a).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show (v - (v - (i : ℤ))).toNat = i
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    show v - (((v - a).toNat : ℕ) : ℤ) = a
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    omega

end Main

theorem uDomA : UDomA := by
  intro F _ _ _ _ _ _ ψ hψ ν _ _
  have hHaar : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  have hRight : (hG ψ).IsMulRightInvariant := by unfold hG; infer_instance
  have hBox : {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} = (GodementSectionLocal.box F 0 : Set (Fin 2 → F)) := by
    ext x
    simp [GodementSectionLocal.mem_box, mem_valBall_zero_iff]
  have hV : V2 ψ ≠ 0 := by
    unfold V2
    rw [hBox]
    exact GlobalTheory.CompanionTheory.LFNe.volume_unit_box_ne_zero ψ
  have hK : (hG ψ).real (integralGL F 2 : Set (GL (Fin 2) F)) ≠ 0 := by
    refine (ENNReal.toReal_ne_zero).2 ⟨?_, (isCompact_integralGL F 2).measure_lt_top.ne⟩
    exact (isOpen_integralGL F 2).measure_ne_zero _ ⟨1, (integralGL F 2).one_mem⟩
  refine ⟨(((hG ψ).real (integralGL F 2 : Set (GL (Fin 2) F)) : ℝ) : ℂ) * ((V2 ψ : ℝ) : ℂ),
    mul_ne_zero (by exact_mod_cast hK) (by exact_mod_cast hV), fun l hl => ?_⟩
  have h01 : l 1 ≤ l 0 := hl (by decide)
  have h12 : l 2 ≤ l 1 := hl (by decide)
  set A' := (l 0 - l 2 + 1).toNat with hA'
  set B := (l 1 - l 2 + 1).toNat with hB
  set S : Finset (Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F])) :=
    (Finset.range A').sigma fun _ => (Finset.range B).sigma fun _ => Finset.univ with hS
  have hcover : ∀ g, f1 ψ ν l g ≠ 0 → ∃ a ∈ S, g * (rowRep a.1 a.2.1 a.2.2)⁻¹ ∈ integralGL F 2 := by
    intro g hg
    obtain ⟨i, j, c, hc⟩ := GlobalTheory.T.integral_matrix_row_rep_exists F g (unramified_vector_support_integral ψ ν l g hg)
    refine ⟨⟨i, j, c⟩, ?_, hc⟩
    have he : g = (g * (rowRep i j c)⁻¹) * rowRep i j c := by group
    rw [he, unramified_vector_left_invariant hψ ν l hc] at hg
    obtain ⟨h1, h2⟩ := unramified_vector_rep_support hψ ν l i j c hg
    simp only [hS, Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true, hA', hB]
    omega
  have hcos := GlobalTheory.T.integral_right_coset_decomposition (GL (Fin 2) F) (hG ψ) (integralGL F 2) (isOpen_integralGL F 2)
    (isCompact_integralGL F 2) (Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F]))
    (fun a => rowRep a.1 a.2.1 a.2.2) S (f1 ψ ν l) (GlobalTheory.T.row_reps_distinct_cosets F)
    (fun κ hκ g => unramified_vector_left_invariant hψ ν l hκ g) hcover
  have hsub : ∫ h, s2 ψ ν h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) *
      inn ψ (Φ0 F) h (torusPow F 3 l) ∂hG ψ = ∫ k, f1 ψ ν l k ∂hG ψ :=
    (integral_mul_right_eq_self (fun h => s2 ψ ν h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) *
      inn ψ (Φ0 F) h (torusPow F 3 l)) (torusPow F 2 ![l 0, l 1])⁻¹).symm
  have hsum : ∑ a ∈ S, f1 ψ ν l (rowRep a.1 a.2.1 a.2.2) =
      ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
        (qF F : ℂ) ^ (l 1 - b).toNat *
          s2 ψ ν (torusPow F 2 ![a, b]) * Cc ψ l (l 0 - a).toNat (l 1 - b).toNat := by
    rw [hS, Finset.sum_sigma]
    simp only [Finset.sum_sigma]
    rw [sum_range_reindex (l 1) (l 0) h01 A' (by omega) _ ?_]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_Icc] at ha
      rw [sum_range_reindex (l 2) (l 1) h12 B le_rfl _ (fun i h1 h2 => absurd h1 h2)]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_Icc] at hb
      have hi : (((l 0 - a).toNat : ℕ) : ℤ) = l 0 - a := Int.toNat_of_nonneg (by omega)
      have hj : (((l 1 - b).toNat : ℕ) : ℤ) = l 1 - b := Int.toNat_of_nonneg (by omega)
      rw [sum_rep hψ ν l _ _ (by omega), if_pos (by omega), hi, hj, sub_sub_cancel, sub_sub_cancel]
    · intro i _ hi
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_range] at hi hj
      rw [sum_rep hψ ν l _ _ (by omega), if_neg (by omega)]
  have hS0 : sqrtQ F ≠ 0 := sqrtQ_ne_zero
  have hterm : ∀ a ∈ Finset.Icc (l 1) (l 0), ∀ b ∈ Finset.Icc (l 2) (l 1),
      (qF F : ℂ) ^ (l 1 - b).toNat *
          s2 ψ ν (torusPow F 2 ![a, b]) * Cc ψ l (l 0 - a).toNat (l 1 - b).toNat =
      sqrtQ F ^ (2 * l 1 + 4 * l 2) * ((V2 ψ : ℝ) : ℂ) *
        evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b]) := by
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    have hi : (((l 0 - a).toNat : ℕ) : ℤ) = l 0 - a := Int.toNat_of_nonneg (by omega)
    have hj : (((l 1 - b).toNat : ℕ) : ℤ) = l 1 - b := Int.toNat_of_nonneg (by omega)
    have hq : (qF F : ℂ) ^ (l 1 - b).toNat = sqrtQ F ^ (2 * (l 1 - b)) := by
      rw [← hj, ← sqrtQ_sq, ← pow_mul, ← zpow_natCast]
      push_cast
      rfl
    rw [(GlobalTheory.T.whittaker_torus_value_formula_holds F ψ hψ ν a b).1 (by omega), hq, Cc, hi, hj]
    have : sqrtQ F ^ (2 * (l 1 - b)) * sqrtQ F ^ (-(a - b)) *
        sqrtQ F ^ (-(3 * (l 0 - a + (l 1 - b) - l 0 - l 1))) *
        sqrtQ F ^ (2 * (2 * l 2 + (l 0 - a) + (l 1 - b) - l 0 - l 1)) =
        sqrtQ F ^ (2 * l 1 + 4 * l 2) := by
      rw [← zpow_add₀ hS0, ← zpow_add₀ hS0, ← zpow_add₀ hS0]
      congr 1
      ring
    rw [← this]
    ring
  have hmp : mp (GeneralLinearGroup.det (torusPow F 3 l)) 1 = sqrtQ F ^ (-(2 * (l 0 + l 1 + l 2))) := by
    have := GlobalTheory.T.unramified_character_uniformizer_power F (l 0 + l 1 + l 2) 2
    have e : (((2 : ℤ) : ℂ) / 2) = 1 := by norm_num
    rw [e] at this
    rw [GlobalTheory.T.det_torus_power, Fin.sum_univ_three, this]
  have hhalf : halfModulus F l = sqrtQ F ^ (2 * l 2 - 2 * l 0) := by
    rw [halfModulus_eq]
    congr 1
    simp [rhoPair, Fin.sum_univ_three]
    ring
  show Wp ψ (s2 ψ ν) (Φ0 F) (torusPow F 3 l) = _
  unfold Wp
  rw [hsub, hcos, hsum, hmp, hhalf, Finset.sum_congr rfl fun a ha =>
    Finset.sum_congr rfl fun b hb => hterm a ha b hb]
  simp only [← Finset.mul_sum]
  have : sqrtQ F ^ (-(2 * (l 0 + l 1 + l 2))) * sqrtQ F ^ (2 * l 1 + 4 * l 2) =
      sqrtQ F ^ (2 * l 2 - 2 * l 0) := by
    rw [← zpow_add₀ hS0]
    congr 1
    ring
  rw [← this]
  ring

end GlobalTheory.CompanionTheory.LFUDom
