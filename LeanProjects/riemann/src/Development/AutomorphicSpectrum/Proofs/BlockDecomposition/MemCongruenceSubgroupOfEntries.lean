import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestVectorNonvanishingLocal
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSecSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem valuation_le_of_mem_valBall {x : F} {m : ℕ} (h : x ∈ valBall F (m : ℤ)) :
    ValuativeRel.valuation F x ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m := by
  obtain ⟨a, ha, rfl⟩ := GodementJacquet.mem_valBall_iff_exists.1 h
  have ha' : ValuativeRel.valuation F a ≤ 1 := ha
  rw [map_mul, map_pow]
  exact mul_le_of_le_one_right' ha'

theorem valuation_eq_one_of_sub_one {x : F} (h : x - 1 ∈ valBall F 1) :
    ValuativeRel.valuation F x = 1 := by
  have h1 : ValuativeRel.valuation F (x - 1) < 1 := mem_valBall_one_iff.1 h
  have h2 : ValuativeRel.valuation F (x - 1) < ValuativeRel.valuation F (1 : F) := by
    simpa using h1
  simpa using Valuation.map_eq_of_sub_lt (ValuativeRel.valuation F) h2

theorem inv_mem_valBall_zero {x : F} (h : ValuativeRel.valuation F x = 1) :
    x⁻¹ ∈ valBall F 0 := by
  refine mem_valBall_zero_iff.2 ?_
  change ValuativeRel.valuation F x⁻¹ ≤ 1
  rw [map_inv₀, h, inv_one]

theorem ne_zero_of_valuation_eq_one {x : F} (h : ValuativeRel.valuation F x = 1) : x ≠ 0 := by
  rintro rfl
  simp at h

theorem mem_zero_of_nat {x : F} {m : ℕ} (h : x ∈ valBall F (m : ℤ)) : x ∈ valBall F 0 :=
  valBall_antitone (by positivity) h

theorem mem_one_of_nat {x : F} {m : ℕ} (hm : 1 ≤ m) (h : x ∈ valBall F (m : ℤ)) :
    x ∈ valBall F 1 :=
  valBall_antitone (by exact_mod_cast hm) h

theorem one_mem_zero : (1 : F) ∈ valBall F 0 := mem_valBall_zero_iff.2 (one_mem _)

theorem mem_zero_of_sub_one {x : F} {m : ℕ} (h : x - 1 ∈ valBall F (m : ℤ)) :
    x ∈ valBall F 0 := by
  simpa using add_mem (mem_zero_of_nat h) (one_mem_zero (F := F))

theorem mem_congruenceSubgroup_of_entries (g : GL (Fin 2) F) {m : ℕ} (hm : 1 ≤ m)
    (h00 : g.val 0 0 - 1 ∈ valBall F (m : ℤ)) (h01 : g.val 0 1 ∈ valBall F (m : ℤ))
    (h10 : g.val 1 0 ∈ valBall F (m : ℤ)) (h11 : g.val 1 1 - 1 ∈ valBall F (m : ℤ)) :
    g ∈ GLnLocal.congruenceSubgroup F 2 m := by
  have i00 : g.val 0 0 ∈ valBall F 0 := mem_zero_of_sub_one h00
  have i11 : g.val 1 1 ∈ valBall F 0 := mem_zero_of_sub_one h11
  have i01 : g.val 0 1 ∈ valBall F 0 := mem_zero_of_nat h01
  have i10 : g.val 1 0 ∈ valBall F 0 := mem_zero_of_nat h10
  have hD : g.val.det - 1 ∈ valBall F 1 := by
    rw [Matrix.det_fin_two]
    have e : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 - 1 =
        (g.val 0 0 - 1) * g.val 1 1 + (g.val 1 1 - 1) - g.val 0 1 * g.val 1 0 := by ring
    rw [e]
    refine sub_mem (add_mem ?_ (mem_one_of_nat hm h11)) ?_
    · simpa using mul_mem_valBall (mem_one_of_nat hm h00) i11
    · simpa using mul_mem_valBall (mem_one_of_nat hm h01) i10
  have hinv := inv_mem_valBall_zero (valuation_eq_one_of_sub_one hD)
  have hinvval : ((g⁻¹ : GL (Fin 2) F)).val = (g.val.det)⁻¹ • Matrix.adjugate g.val := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have mulz : ∀ {y : F}, y ∈ valBall F 0 → (g.val.det)⁻¹ * y ∈ 𝒪[F] := fun hy =>
    mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall hinv hy)
  rw [GLnLocal.mem_congruenceSubgroup_iff, GLnLocal.mem_integralGL_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact mem_valBall_zero_iff.1 i00
    · exact mem_valBall_zero_iff.1 i01
    · exact mem_valBall_zero_iff.1 i10
    · exact mem_valBall_zero_iff.1 i11
  · change ((g⁻¹ : GL (Fin 2) F)).val i j ∈ 𝒪[F]
    rw [hinvval, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa using mulz i11
    · simpa using mulz (neg_mem i01)
    · simpa using mulz (neg_mem i10)
    · simpa using mulz i00
  · fin_cases i <;> fin_cases j
    · simpa using valuation_le_of_mem_valBall h00
    · simpa using valuation_le_of_mem_valBall h01
    · simpa using valuation_le_of_mem_valBall h10
    · simpa using valuation_le_of_mem_valBall h11

theorem exists_decomp (h : GL (Fin 2) F) (hd : h.val 1 1 ≠ 0) :
    ∃ (a : Fˣ) (k : GL (Fin 2) F), (a : F) = h.val.det / h.val 1 1 ∧
      k.val = !![1, 0; h.val 1 0, h.val 1 1] ∧
      h = uni2 (h.val 0 1 / h.val 1 1) * (dg2 a 1 * k) := by
  have hdet : h.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero
  refine ⟨Units.mk0 (h.val.det / h.val 1 1) (div_ne_zero hdet hd),
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; h.val 1 0, h.val 1 1]
      (by simpa [Matrix.det_fin_two] using hd), rfl, rfl, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two, Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible] <;>
    field_simp <;> ring

theorem exists_decomp_congruence {m : ℕ} (hm : 1 ≤ m) (h : GL (Fin 2) F)
    (h10 : h.val 1 0 ∈ valBall F (m : ℤ)) (h11 : h.val 1 1 - 1 ∈ valBall F (m : ℤ)) :
    h.val 1 1 ≠ 0 ∧ ∃ (a : Fˣ) (k : GL (Fin 2) F), (a : F) = h.val.det / h.val 1 1 ∧
      k.val = !![1, 0; h.val 1 0, h.val 1 1] ∧ k ∈ GLnLocal.congruenceSubgroup F 2 m ∧
      h = uni2 (h.val 0 1 / h.val 1 1) * (dg2 a 1 * k) := by
  have hv := valuation_eq_one_of_sub_one (mem_one_of_nat hm h11)
  have hd := ne_zero_of_valuation_eq_one hv
  obtain ⟨a, k, ha, hk, e⟩ := exists_decomp h hd
  refine ⟨hd, a, k, ha, hk, ?_, e⟩
  refine mem_congruenceSubgroup_of_entries k hm ?_ ?_ ?_ ?_ <;> rw [hk]
  · simp
  · simp
  · simpa using h10
  · simpa using h11

theorem diag_mul_lower_triangular_val (a : Fˣ) (k : GL (Fin 2) F) {c d : F} (hk : k.val = !![1, 0; c, d]) :
    (dg2 a 1 * k).val = !![(a : F), 0; c, d] := by
  rw [Units.val_mul, hk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul_lower_entries (x : F) (g : GL (Fin 2) F) (j : Fin 2) :
    (uni2 x * g).val 1 j = g.val 1 j := by
  fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

variable [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_det_half_eq_one {n : ℕ} (hn : 1 ≤ n) {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 n) :
    mp (Matrix.GeneralLinearGroup.det u) (1 / 2) = 1 := by
  have hD : ((Matrix.GeneralLinearGroup.det u : Fˣ) : F) - 1 ∈ valBall F 1 := by
    have e := fun i j => GodementSectionLocal.sub_one_mem_valBall_of_mem_congruenceSubgroup hu i j
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    have e2 : u.val 0 0 * u.val 1 1 - u.val 0 1 * u.val 1 0 - 1 =
        (u.val 0 0 - 1) * u.val 1 1 + (u.val 1 1 - 1) - u.val 0 1 * u.val 1 0 := by ring
    rw [e2]
    refine sub_mem (add_mem ?_ (mem_one_of_nat hn h11)) ?_
    · simpa using mul_mem_valBall (mem_one_of_nat hn h00) (mem_zero_of_sub_one h11)
    · simpa using mul_mem_valBall (mem_one_of_nat hn h01) (mem_zero_of_nat h10)
  have hv := valuation_eq_one_of_sub_one hD
  have h1 : ((Matrix.GeneralLinearGroup.det u : Fˣ) : F) ∈ 𝒪[F] := by
    change ValuativeRel.valuation F _ ≤ 1
    exact hv.le
  have h2 : (((Matrix.GeneralLinearGroup.det u)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_inv_eq_inv_val]
    exact mem_valBall_zero_iff.1 (inv_mem_valBall_zero hv)
  have hmod := GlobalTheory.CompanionTheory.LocalTestVectors.modulus_eq_one_of_integral h1 h2
  unfold mp
  rw [hmod]
  simp

theorem support_and_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (W : GL (Fin 3) F → ℂ) (n m : ℕ) (C c : ℂ), 1 ≤ n → n ≤ m →
  (∀ (y : F) (g : GL (Fin 2) F), W' (uni2 y * g) = (ψ y : ℂ) * W' g) →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  (∀ a : Fˣ, (a : F) - 1 ∈ valBall F (n : ℤ) → W' (dg2 a 1) = C) →
  (∀ a : Fˣ, (a : F) - 1 ∉ valBall F (n : ℤ) → W' (dg2 a 1) = 0) →
  (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    W (GL2LocalData.em h) = c * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) →
  (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) → W (GL2LocalData.em h) = 0) →
  (∀ h, W (GL2LocalData.em h) ≠ 0 → ∃ x : F, ∃ u : GL (Fin 2) F, (u ∈ GLnLocal.congruenceSubgroup F 2 n ∧ u.val 1 0 ∈ valBall F (m : ℤ) ∧ u.val 1 1 - 1 ∈ valBall F (m : ℤ)) ∧ h = uni2 x * u) ∧
  ∀ (x : F) (u : GL (Fin 2) F), u ∈ GLnLocal.congruenceSubgroup F 2 n → u.val 1 0 ∈ valBall F (m : ℤ) → u.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    W (GL2LocalData.em (uni2 x * u)) = (ψ x : ℂ) * (c * C) := by
  intro F _ _ _ _ _ _ ψ hψ W' W n m C c hn hnm hpsi hinv hC h0 hval hzero
  have hm : 1 ≤ m := hn.trans hnm
  have ball : ∀ {x : F}, x ∈ valBall F (m : ℤ) → x ∈ valBall F (n : ℤ) := fun h =>
    valBall_antitone (by exact_mod_cast hnm) h
  refine ⟨fun h hne => ?_, fun x u hu u10 u11 => ?_⟩
  · have hrow : h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ) := by
      by_contra hcon
      exact hne (hzero h hcon)
    obtain ⟨h10, h11⟩ := hrow
    obtain ⟨-, a, k, -, hk, hkm, e⟩ := exists_decomp_congruence hm h h10 h11
    have hW : W' h ≠ 0 := by
      intro h00
      apply hne
      rw [hval h h10 h11, h00, mul_zero]
    have hWa : W' (dg2 a 1) ≠ 0 := by
      intro h00
      apply hW
      rw [e, hpsi, hinv _ k hkm, h00, mul_zero]
    have ha : (a : F) - 1 ∈ valBall F (n : ℤ) := by
      by_contra hcon
      exact hWa (h0 a hcon)
    have hv := diag_mul_lower_triangular_val a k hk
    refine ⟨h.val 0 1 / h.val 1 1, dg2 a 1 * k, ⟨?_, ?_, ?_⟩, e⟩
    · refine mem_congruenceSubgroup_of_entries _ hn ?_ ?_ ?_ ?_ <;> rw [hv]
      · simpa using ha
      · simp
      · simpa using ball h10
      · simpa using ball h11
    · rw [hv]; simpa using h10
    · rw [hv]; simpa using h11
  · have e := fun i j => GodementSectionLocal.sub_one_mem_valBall_of_mem_congruenceSubgroup hu i j
    have h00 := e 0 0
    have h01 := e 0 1
    simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero] at h00 h01
    obtain ⟨hd, a, k, ha, hk, hkm, ed⟩ := exists_decomp_congruence hm u u10 u11
    have hv1 := valuation_eq_one_of_sub_one (mem_one_of_nat hm u11)
    have hdi := inv_mem_valBall_zero hv1
    have hy : u.val 0 1 / u.val 1 1 ∈ 𝒪[F] := by
      rw [div_eq_mul_inv]
      exact mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall (mem_zero_of_nat h01) hdi)
    have hψy : (ψ (u.val 0 1 / u.val 1 1) : ℂ) = 1 :=
      GlobalTheory.CompanionTheory.SphOne.coe_eq_one_of_isStd hψ _ hy
    have ha1 : (a : F) - 1 ∈ valBall F (n : ℤ) := by
      have e3 : (a : F) - 1 =
          ((u.val 0 0 - 1) * u.val 1 1 - u.val 0 1 * u.val 1 0) * (u.val 1 1)⁻¹ := by
        rw [ha, Matrix.det_fin_two]
        field_simp
        ring
      rw [e3]
      have t1 : (u.val 0 0 - 1) * u.val 1 1 ∈ valBall F (n : ℤ) := by
        simpa using mul_mem_valBall h00 (mem_zero_of_sub_one u11)
      have t2 : u.val 0 1 * u.val 1 0 ∈ valBall F (n : ℤ) := by
        simpa using mul_mem_valBall h01 (mem_zero_of_nat u10)
      simpa using mul_mem_valBall (sub_mem t1 t2) hdi
    have hWu : W' u = C := by
      rw [ed, hpsi, hinv _ k hkm, hC a ha1, hψy, one_mul]
    have r10 : (uni2 x * u).val 1 0 ∈ valBall F (m : ℤ) := by rw [unipotent_mul_lower_entries]; exact u10
    have r11 : (uni2 x * u).val 1 1 - 1 ∈ valBall F (m : ℤ) := by rw [unipotent_mul_lower_entries]; exact u11
    rw [hval _ r10 r11, GlobalTheory.CompanionTheory.WhittakerPsi.det_left_unipotent_mul, mp_det_half_eq_one hn hu, hpsi, hWu]
    ring

end GlobalTheory.CompanionTheory.SmallSecSupp
