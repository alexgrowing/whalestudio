import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm :
    ∀ c : ℝ, 0 < c → ∃ (S : Set (A ℚ)ˣ) (Bu : ℝ), IsCompact S ∧ 1 ≤ Bu ∧ ∀ a : (A ℚ)ˣ, c ≤ ab a →
        ∃ (q : ℚ) (a' u : (A ℚ)ˣ), q ≠ 0 ∧ (a' : A ℚ) = rt q * (a : A ℚ) ∧ u ∈ S ∧ (a' : A ℚ).2 = (u : A ℚ).2 ∧
          ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 ∧ Bu⁻¹ ≤ |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ∧
          |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ≤ Bu * (ab a / c) := by
  intro c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) hc c
  have hv : Continuous fun u : IdeleGroup ℚ => ((u : IdeleGroup ℚ) : A ℚ) := Units.continuous_val
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ)) : A ℚ) := Units.continuous_coe_inv
  have hcont : Continuous fun u : IdeleGroup ℚ => ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ +
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ :=
    (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hv))).add
      (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hi)))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  set b := max M 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : 0 < b := one_pos.trans_le hb1
  refine ⟨S, b, hS, hb1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := ab a / c with hsdef
  have hs0 : 0 < s := one_pos.trans_le hx
  set p : IdeleGroup ℚ := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, Module.finrank_self, pow_one]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal ℚ t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs0 v
  have hpi2 : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul p)
    rwa [hp2, mul_one] at e
  have hre : |UpperTheory.ConvolutionTheory.RankTwoDescent.re (((p * u : IdeleGroup ℚ)) : A ℚ)| = s * ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := by
    rw [abs_re]
    have e1 : (((p * u : IdeleGroup ℚ)) : A ℚ).1 Rat.infinitePlace =
        ((p : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace := by
      simp only [Units.val_mul]
      rfl
    rw [e1, norm_mul, hp, norm_posIdele_infinite]
  have hbd := hM u ht
  have hn1 : 0 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity)] at hbd
  have hMb : M ≤ b := le_max_left _ _
  have hprod : ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ *
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ = 1 := by
    rw [← norm_mul]
    have e : ((u : IdeleGroup ℚ) : A ℚ).1 * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 = 1 :=
      congrArg Prod.fst (Units.mul_inv u)
    have e' := congrFun e Rat.infinitePlace
    change ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace = 1 at e'
    rw [e', norm_one]
  refine ⟨(t : ℚ), p * u, u, t.ne_zero, ?_, ht, ?_, ?_, ?_, ?_⟩
  · have h1 : ((IdeleGroup.diagonal ℚ t : IdeleGroup ℚ) : A ℚ) = rt (t : ℚ) := IdeleGroup.coe_diagonal _ _
    rw [← hau, Units.val_mul, h1]
  · change (((p * u : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [Units.val_mul]
    change (((p : IdeleGroup ℚ) : A ℚ)).2 * _ = _
    rw [hp2, one_mul]
  · change ((((p * u)⁻¹ : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [_root_.mul_inv_rev, Units.val_mul]
    change _ * (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = _
    rw [hpi2, mul_one]
  · rw [hre, inv_le_iff_one_le_mul₀ hb0]
    have h1 : 1 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ * b := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left (by linarith) hn1
    nlinarith
  · rw [hre, mul_comm b]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
