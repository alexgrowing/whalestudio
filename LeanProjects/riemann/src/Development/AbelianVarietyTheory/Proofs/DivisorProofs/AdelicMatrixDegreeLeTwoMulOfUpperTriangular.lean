import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinaryFormSplitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeSymmetricPowerFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeTwistFamilyAtPlaceByScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeGeOfTwistedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeEqSumOfScalarSplitStatement

set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem GlobalTheory.Nef.deg_le_two_mul_of_triangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  intro k F _ _ _ _ _ hFF g hg htri b hb
  by_cases hne : IsEmpty (Place k F)
  · have h0 : deg g = 0 := by simp [deg, finsum_of_isEmpty]
    have hres : IsRes (k := k) (F := F) (E := F) id := fun p x => by simp
    have hw : (![1, 0] : Fin 2 → F) ≠ 0 := by intro h; simpa using congrFun h 0
    have h1 := hb F id hres ![1, 0] hw
    have hl : degLine (pullAd id g) (![1, 0] : Fin 2 → F) = 0 := by simp [degLine, finsum_of_isEmpty]
    rw [hl] at h1
    simp at h1
    rw [h0]; push_cast; linarith
  rw [not_isEmpty_iff] at hne
  obtain ⟨v₀⟩ := hne
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_section_of_large_adelic_degree k F hFF
  obtain ⟨π, hπ0, hπ⟩ := (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v₀).2.2.2.2.2.1
  have key : ∀ m : ℕ, ((m * (m + 1) / 2 : ℕ) : ℝ) * (deg g : ℝ) ≤ (m + 1) * (m * b + 1 + γ) := by
    intro m
    set N : ℕ := m * (m + 1) / 2 with hN
    set S : Place k F → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun v => symMat m (g v) with hS
    obtain ⟨hSadm, hSdeg⟩ := GlobalTheory.Nef.admissible_degree_symmetricPowerFamily k F m g hg htri
    rw [← hN] at hSdeg
    set D : ℤ := (N : ℤ) * deg g - (m + 1) * γ - 1 with hD
    set e : ℤ := D / (m + 1) with he
    have hm0 : (0 : ℤ) < m + 1 := by positivity
    have hdiv := Int.mul_ediv_add_emod D (m + 1)
    have hmod0 := Int.emod_nonneg D hm0.ne'
    have hmod1 := Int.emod_lt_of_pos D hm0
    rw [← he] at hdiv
    obtain ⟨hTadm, hTdeg⟩ := GlobalTheory.Nef.admissible_degree_twistFamilyAtPlaceByScalar k F (m + 1) S hSadm v₀ π hπ0 hπ e
    have hdegT : ((m + 1 : ℕ) : ℤ) * γ < deg (twistAt v₀ (π ^ (-e)) S) := by
      have hc1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hTdeg, hSdeg, hc1]; linarith
    obtain ⟨p, hp0, hpint⟩ := hγ (m + 1) _ hTadm hdegT
    have hep : e ≤ degLine S p := GlobalTheory.T.lineDegree_ge_of_twisted_section k F hFF (m + 1) S hSadm v₀ π hπ0 hπ e p hp0 hpint
    obtain ⟨E, _, _, _, c, s, t, hc, hst, hid⟩ := GlobalTheory.T.exists_binary_form_eq_mul_prod_linear F m p hp0
    letI : Algebra k E := ((algebraMap F E).comp (algebraMap k F)).toAlgebra
    haveI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).1
    have hEFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hFF).2 E
    have pS := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ (m + 1) S hSadm
    have pg := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ 2 g hg
    have hpull : pullAd ρ S = fun P => symMat m (pullAd ρ g P) := by
      funext P; simp only [pullAd, hS, symMat_map]
    have htriE : ∀ P, pullAd ρ g P 1 0 = 0 := by intro P; simp [pullAd, htri]
    set q : Fin (m + 1) → E := fun i => algebraMap F E (p i) with hq
    have hpt : ∀ P, ordVec P ((symMat m (pullAd ρ g P)).mulVec q) =
        ord P c + ∑ j, ordVec P ((pullAd ρ g P).mulVec ![s j, t j]) := fun P =>
      GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder k E P m _ (htriE P) (pg.1.1 P) q c s t hc hst (by
        have h3 := hid E[X] (C ((pullAd ρ g P) 0 0)) (C ((pullAd ρ g P) 0 1) + C ((pullAd ρ g P) 1 1) * X)
        rw [Polynomial.algebraMap_eq] at h3
        exact h3)
    have h6 := GlobalTheory.T.lineDegree_eq_sum_of_scalar_split k E hEFF m (m + 1) (pullAd ρ g) pg.1 (fun P => symMat m (pullAd ρ g P)) q c
      (fun j => ![s j, t j]) hc hst hpt
    have h2 := pS.2.2.1 p hp0
    rw [hpull] at h2
    have hbound : ∀ j, (degLine (pullAd ρ g) ![s j, t j] : ℝ) ≤ b * Module.finrank F E :=
      fun j => hb E ρ hρ _ (hst j)
    have hsum : ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) ≤ m * (b * Module.finrank F E) := by
      push_cast
      calc (∑ j : Fin m, (degLine (pullAd ρ g) ![s j, t j] : ℝ)) ≤ ∑ _j : Fin m, b * Module.finrank F E :=
            Finset.sum_le_sum fun j _ => hbound j
        _ = m * (b * Module.finrank F E) := by simp
    have hfr : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
    have h7 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ m * (b * Module.finrank F E) := by
      have h8 : (Module.finrank F E : ℤ) * degLine S p = ∑ j, degLine (pullAd ρ g) ![s j, t j] := by
        rw [← h6, ← h2]
      have h8' : (Module.finrank F E : ℝ) * (degLine S p : ℝ) = ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) := by
        exact_mod_cast h8
      have h9 : (e : ℝ) ≤ (degLine S p : ℝ) := by exact_mod_cast hep
      have h10 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (degLine S p : ℝ) :=
        mul_le_mul_of_nonneg_left h9 hfr.le
      linarith
    have hemb : (e : ℝ) ≤ m * b := by
      have : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (m * b) := by linarith
      exact le_of_mul_le_mul_left this hfr
    have hint : (N : ℤ) * deg g ≤ (m + 1) * (e + 1 + γ) := by linarith
    have hreal : ((N : ℤ) : ℝ) * (deg g : ℝ) ≤ ((m : ℝ) + 1) * ((e : ℝ) + 1 + γ) := by exact_mod_cast hint
    push_cast at hreal
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hpos : (0 : ℝ) < (deg g : ℝ) - 2 * b := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (1 + γ) / ((deg g : ℝ) - 2 * b))
  have hk := key m
  have hN : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) / 2 := by
    have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  rw [hN] at hk
  rw [div_lt_iff₀ hpos] at hm
  have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : (m : ℝ) * (deg g : ℝ) ≤ 2 * (m * b + 1 + γ) := by
    have h3 : ((m : ℝ) + 1) * ((m : ℝ) * (deg g : ℝ)) ≤ ((m : ℝ) + 1) * (2 * (m * b + 1 + γ)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hm'
  nlinarith
