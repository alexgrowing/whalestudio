import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementA
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M MvPolynomial Finset

theorem partner_determinant_holds : PartnerDet := by
  intro p _ Vs _ _ _ _ be k g D hli hpart
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG
  obtain ⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩ := Formalism.GM.TM.smith_qp smith_form_p_adic_integers G
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  let U' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨U x y, hU x y⟩
  let V' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨V x y, hV x y⟩
  have hU'map : U'.map φ = U := by ext x y; rfl
  have hU'det : IsUnit U'.det := by
    rw [PadicInt.isUnit_iff]
    have : ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det := by
      rw [← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]; rfl
    rw [PadicInt.norm_def, this, hUd]
  set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW
  have hWU : W * U' = 1 := Matrix.nonsing_inv_mul _ hU'det
  have hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x := fun a x => by
    rw [← PadicInt.algebraMap_apply, algebraMap_smul]

  have hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖ := by
    intro i
    set u : Vs := ∑ a, W i a • g a with hu
    have huL : u ∈ Submodule.span ℤ_[p] (Set.range g) :=
      Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩
    have hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a := by
      intro a x hx hux
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx
      have h0 : ∑ b, (W i b - a * c b) • g b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [← hu, hux, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0
      have h2 : (W * U') i i = a * ∑ b, c b * U' b i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sub_eq_zero.mp (h1 b)]; ring
      rw [hWU, Matrix.one_apply_eq] at h2
      exact IsUnit.of_mul_eq_one _ h2.symm
    obtain ⟨u', hu'L, hu'⟩ := hpart u huL hprim
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L
    have hWG : ∀ b, be u (g b) = dg i * V i b := by
      intro b
      have e1 : be u (g b) = ((W.map φ) * G) i b := by
        rw [Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
      have e2 : (W.map φ) * U = 1 := by
        rw [← hU'map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      rw [e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]
    have hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p]) := by
      rw [map_sum, PadicInt.coe_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]
      show _ = dg i * ((c b : ℚ_[p]) * V i b)
      ring
    rw [hval, norm_mul] at hu'
    refine hu'.trans ?_
    calc ‖dg i‖ * ‖((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])‖ ≤ ‖dg i‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖dg i‖ := mul_one _
  rw [hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one,
    norm_prod]
  calc (p : ℝ) ^ (-(D * k)) = ∏ _i : Fin k, (p : ℝ) ^ (-D) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]
        congr 1; ring
    _ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i

section Gr
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem grLat_le_int (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ IntPol p (Fin (K + 1) × Fin r) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ IntPol p (Fin (K + 1) × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2
  refine Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_
  rw [Formalism.GM.MeanGammaLemmas.coeff_initPart]
  split_ifs
  · exact Formalism.CountingSumsFrames.intPol_norm f hfI m
  · simp

theorem grLat_le_pol (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfM : f ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hfP : f ∈ Pol p r LLw :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1
  show initPart v e f ∈ Pol p r LLw
  unfold Pol at hfP ⊢
  rw [mem_restrictSupport_iff] at hfP ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart] at hm
  refine hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
  intro h0
  apply hm
  rw [h0, ite_self]

end Gr

theorem graded_piece_bound_holds : GradedPieceBound := by
  intro p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Pr, hPr⟩ := hProj
  have key := partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli
    ?_
  · exact key
  intro u hu hprim
  rw [hspan] at hu hprim
  set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr
  set XX := grSpan p LLw J M ρ w e with hXX
  have hGX : ∀ x ∈ Gr, x ∈ XX := fun x hx => Submodule.subset_span hx
  have hu0 : u ≠ 0 := by
    intro h0
    have := hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])
    exact not_isUnit_zero this
  have huI : u ∈ IntPol p (Fin (K + 1) × Fin r) := grLat_le_int LLw J M ρ w _ e hu
  have huP : u ∈ Pol p r LLw := grLat_le_pol LLw J M ρ w _ e hu
  have hne : u.support.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image u.support (fun m => ‖coeff m u‖) hne
  set a := coeff m u with ha
  have ha0 : a ≠ 0 := mem_support_iff.mp hm
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hmD : MultiDeg LLw m := by
    unfold Pol at huP
    rw [mem_restrictSupport_iff] at huP
    exact huP (Finset.mem_coe.mpr hm)
  set u0 := a⁻¹ • u with hu0def
  have hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_
    rw [hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]
    by_cases hm' : m' ∈ u.support
    · exact hmax m' hm'
    · rw [notMem_support_iff.mp hm', norm_zero]; exact han.le
  have hu0X : u0 ∈ XX := XX.smul_mem _ (hGX u hu)
  have hu0c : ‖coeff m u0‖ = 1 := by
    rw [hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]
  have huu0 : u = a • u0 := by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr := hSat u0 hu0X hu0I
  have hpc : ((p : ℚ_[p]) ^ c) ≠ 0 := pow_ne_zero _ hpQ
  have hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]
  have hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]

  have hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1 := by
      rw [norm_div, hnpc, div_inv_eq_mul]
      have hpc' : (0 : ℝ) < (p : ℝ) ^ c := by positivity
      calc ‖a‖ * (p : ℝ) ^ c < ((p : ℝ) ^ c)⁻¹ * (p : ℝ) ^ c := mul_lt_mul_of_pos_right hlt hpc'
        _ = 1 := inv_mul_cancel₀ hpc'.ne'
    let b : ℤ_[p] := ⟨a / (p : ℚ_[p]) ^ c, hb.le⟩
    have hub : u = b • (((p : ℚ_[p]) ^ c) • u0) := by
      rw [← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]
      show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0
      rw [div_mul_cancel₀ _ hpc]; exact huu0
    have hunit := hprim b _ hy hub
    rw [PadicInt.isUnit_iff] at hunit
    have : ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖ := rfl
    linarith
  obtain ⟨hP1, hP2, hP3⟩ := hPr m hmD
  refine ⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩
  · rw [hspan]
    exact hSat _ (XX.smul_mem _ hP1) hP2
  · rw [Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']
    have e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1) := by
      unfold fockN
      rw [hP3 u (hGX u hu)]
      conv_lhs => rw [huu0]
      rw [Formalism.GM.TM.fock_smul_left, mul_div_assoc]
    have e2 := Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c
    rw [e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]
    have hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹ := by positivity
    have hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹ := by positivity
    have h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    gcongr

end Formalism.InvariantFactorPaths.L4
