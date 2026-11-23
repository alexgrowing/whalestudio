import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem pos_snd (s : ℝ) (hs : 0 < s) :
    (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).2 = 1 := by
  apply RestrictedProduct.ext
  intro v
  exact GroundTheory.Automorphic.Reduction.posIdele_finite s hs v

private theorem pos_inv_snd (s : ℝ) (hs : 0 < s) :
    ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).2 = 1 := by
  have e : ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).2 *
      (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul (GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E))
  rwa [pos_snd, mul_one] at e

private theorem norm_pos_inv (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ‖((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).1 w‖ = s⁻¹ := by
  have e : ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).1 w *
      (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).1 w = 1 :=
    congrArg (fun z : A E => z.1 w) (Units.inv_mul (GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E))
  have h := congrArg norm e
  rw [norm_mul, GroundTheory.Automorphic.Reduction.norm_posIdele_infinite, norm_one] at h
  exact eq_inv_of_mul_eq_one_left h

variable [IsTotallyComplex E]

private theorem norm_pInf (x : A E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ := by
  have e : pInf E x w = InfinitePlace.Completion.extensionEmbedding w (x.1 w) := by
    have h := UpperTheory.V.Cm.infEq_apply (pInf E x) w
    rw [show infEq E (pInf E x) = x.1 from (infEq E).apply_symm_apply x.1] at h
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply (IsTotallyComplex.isComplex w), h,
      RingEquiv.apply_symm_apply]
  rw [e]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

private theorem norm_toL_mD_le (q : (A E)ˣ) {r : ℝ} (hr : 0 ≤ r) (h1 : ∀ w, ‖(q : A E).1 w‖ ≤ r)
    (h2 : ∀ w, ‖((q⁻¹ : (A E)ˣ) : A E).1 w‖ ≤ r) :
    ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (gl (mD q))).val‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => (pi_norm_le_iff_of_nonneg hr).2 fun j =>
    (pi_norm_le_iff_of_nonneg hr).2 fun w => ?_
  change ‖pInf E ((mD q).1 i j) w‖ ≤ r
  rw [norm_pInf]
  fin_cases i <;> fin_cases j
  · simpa using h1 w
  · refine le_trans (le_of_eq ?_) hr
    simp
    first | exact norm_zero | rfl
  · refine le_trans (le_of_eq ?_) hr
    simp
    first | exact norm_zero | rfl
  · simpa using h2 w

end SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_compact_siegel_decomposition_height_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (c : ℝ), 0 < c → ∃ (Y : Set (G1 E)) (C₂ : ℝ), IsCompact Y ∧ ∀ (u : A E) (b : (A E)ˣ), c ≤ ab b → ∃ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (z : GL (Fin 2) (Cinf E)), ∃ w ∈ Y, gl (nU u * mD b) = gl (ratS E γ) * infGL E 2 z * gl w ∧ Ht z ≤ C₂ * ab b := by
  intro E _ _ _ c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := E) hc c
  have hcont : Continuous fun x : InfiniteAdeleRing E => ∑ w : InfinitePlace E, ‖x w‖ :=
    continuous_finset_sum _ fun w _ => continuous_norm.comp (continuous_apply w)
  obtain ⟨M, hM⟩ := (isCompact_closure_fundamentalSetInfinite E).exists_bound_of_continuousOn hcont.continuousOn
  let L : Set (A E) := ((homeomorphMixedSpace E) ⁻¹' Metric.closedBall 0 M) ×ˢ
    (integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E))
  have hL : IsCompact L :=
    ((homeomorphMixedSpace E).isCompact_preimage.2 (isCompact_closedBall _ _)).prod
      (isCompact_integralFiniteAdeles E)
  refine ⟨(fun x : A E × IdeleGroup E => nU x.1 * mD x.2) '' (L ×ˢ S), 3 / c, (hL.prod hS).image
    ((continuous_nU.comp continuous_fst).mul (continuous_mD.comp continuous_snd)), fun u b hb => ?_⟩
  set d := Module.finrank ℚ E
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  have hx : 1 ≤ ab b / c := (one_le_div hc).2 hb
  set s := (ab b / c) ^ (d : ℝ)⁻¹
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by positivity)
  have hs0 : 0 < s := one_pos.trans_le hs1
  have hsd : s ^ d = ab b / c := Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd
  set p : IdeleGroup E := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule E (p⁻¹ * b) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule E (p⁻¹ * b) : ℝ) =
        ((IdeleGroup.ideleModule E p : ℝ))⁻¹ * (IdeleGroup.ideleModule E b : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab b := hc.trans_le hb
    rw [h1, hp, ideleModule_posIdele, hsd]
    change (ab b / c)⁻¹ * ab b = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set a : (A E)ˣ := IdeleGroup.diagonal E t with ha
  set w0 : IdeleGroup E := a * (p⁻¹ * b) with hw0
  have hb' : b = a⁻¹ * p * w0 := by
    rw [hw0, mul_assoc, mul_left_comm p, mul_inv_cancel_left, inv_mul_cancel_left]
  set v : A E := (a : A E) ^ 2 * u with hv
  obtain ⟨f, hf, -⟩ := existsUnique_sub_mem_fundamentalSet E v
  set u2 : A E := v - rt f with hu2
  set u3 : A E := (((p⁻¹ : IdeleGroup E) : (A E)ˣ) : A E) ^ 2 * u2 with hu3
  have h1 : nU u * mD a⁻¹ = mD a⁻¹ * nU v := by
    rw [mD_mul_nU a⁻¹ v]
    congr 2
    rw [hv, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have h2 : nU v = nU (rt f) * nU u2 := by
    rw [← nU_add, hu2, add_sub_cancel]
  have h3 : nU u2 * mD p = mD p * nU u3 := by
    rw [mD_mul_nU p u3]
    congr 2
    rw [hu3, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  have hdec : nU u * mD b = (mD a⁻¹ * nU (rt f)) * mD p * (nU u3 * mD w0) := by
    calc nU u * mD b = (nU u * mD a⁻¹) * mD p * mD w0 := by rw [hb', mD_mul, mD_mul]; simp only [mul_assoc]
      _ = mD a⁻¹ * nU (rt f) * (nU u2 * mD p) * mD w0 := by rw [h1, h2]; simp only [mul_assoc]
      _ = _ := by rw [h3]; simp only [mul_assoc]
  have hG : mD a⁻¹ * nU (rt f) ∈ Gam E := by
    refine (Gam E).mul_mem ?_ (nU_rt_mem f)
    rw [mD_inv]
    exact (Gam E).inv_mem (mD_diagonal_mem t)
  obtain ⟨γ, hγ⟩ := hG
  have hu3L : u3 ∈ L := by
    have hpw : ∀ w, ‖u3.1 w‖ ≤ ‖u2.1 w‖ := fun w => by
      have e : u3.1 w = ((((p⁻¹ : IdeleGroup E) : A E)).1 w) ^ 2 * u2.1 w := rfl
      rw [e, norm_mul, norm_pow, hp, norm_pos_inv]
      have : (s⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hs1)
      nlinarith [norm_nonneg (u2.1 w)]
    refine ⟨?_, ?_⟩
    · refine mem_closedBall_zero_iff.2 ?_
      refine (GJGlobal.norm_homeomorphMixedSpace_le_sum u3.1).trans ?_
      refine (Finset.sum_le_sum fun w _ => hpw w).trans ?_
      exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u2.1 (subset_closure hf.1)))
    · have e : u3.2 = ((((p⁻¹ : IdeleGroup E) : A E)).2) ^ 2 * u2.2 := rfl
      rw [e, hp, pos_inv_snd, one_pow, one_mul]
      exact hf.2
  let z : GL (Fin 2) (Cinf E) := Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p))
  have hz : infGL E 2 z = gl (mD p) := by
    refine ga_ext (pInf_infGL z) ?_
    rw [pFin_infGL]
    have hpf : pFin E (p : A E) = 1 := pos_snd s hs0
    have hpfi : pFin E (((p⁻¹ : IdeleGroup E) : (A E)ˣ) : A E) = 1 := pos_inv_snd s hs0
    refine Units.ext (Matrix.ext fun i j => ?_)
    change (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((mD p).1 i j)
    fin_cases i <;> fin_cases j <;> simp [hpf, hpfi]
  refine ⟨γ, z, nU u3 * mD w0, ⟨(u3, w0), ⟨hu3L, ht⟩, rfl⟩, ?_, ?_⟩
  · rw [hdec, ← hγ, hz]
    exact Units.ext rfl
  · have hsi : s⁻¹ ≤ s := (inv_le_one_of_one_le₀ hs1).trans hs1
    have hle1 : ‖toL z.val‖ ≤ s := norm_toL_mD_le p hs0.le
      (fun w => (norm_posIdele_infinite s hs0 w).le) (fun w => (norm_pos_inv s hs0 w).le.trans hsi)
    have hzi : z⁻¹ = Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p⁻¹)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      have e : gl (mD p) * gl (mD p⁻¹) = 1 := by
        have e1 : mD p * mD p⁻¹ = 1 := by rw [← mD_mul, mul_inv_cancel, mD_one]
        have e2 : gl (mD p) * gl (mD p⁻¹) = gl (mD p * mD p⁻¹) := Units.ext rfl
        rw [e2, e1]
        exact Units.ext rfl
      change Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p)) * _ = 1
      rw [← map_mul, e, map_one]
    have hle2 : ‖toL (z⁻¹).val‖ ≤ s := by
      rw [hzi]
      refine norm_toL_mD_le p⁻¹ hs0.le (fun w => (norm_pos_inv s hs0 w).le.trans hsi) fun w => ?_
      rw [inv_inv]
      exact (norm_posIdele_infinite s hs0 w).le
    have hss : s ≤ ab b / c := hsd ▸ le_self_pow₀ hs1 hd
    have e3 : 3 / c * ab b = 3 * (ab b / c) := by ring
    have e4 : Ht z = 1 + ‖toL z.val‖ + ‖toL (z⁻¹).val‖ := rfl
    rw [e3, e4]
    linarith
