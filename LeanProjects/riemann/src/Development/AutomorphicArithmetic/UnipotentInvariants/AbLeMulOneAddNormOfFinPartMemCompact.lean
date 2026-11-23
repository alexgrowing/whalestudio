import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

open scoped nonZeroDivisors in

private theorem one_le_of_mem {d : 𝓞 ℚ} (hd0 : d ≠ 0) {e : ℚ} (he : e ≠ 0)
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ d * e) ∈
      integralFiniteAdeles (𝓞 ℚ) ℚ) :
    1 ≤ |((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ)| * |(e : ℝ)| := by
  have h2 : algebraMap (𝓞 ℚ) ℚ d * e ∈ ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe r)
  have hdK : algebraMap (𝓞 ℚ) ℚ d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hd0
  have hnq : (n : ℚ) = algebraMap (𝓞 ℚ) ℚ d * e := by
    rw [← hr]
    exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : algebraMap (𝓞 ℚ) ℚ d * e ≠ 0 := mul_ne_zero hdK he
    exact this (by simpa using hnq.symm)
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  rw [← abs_mul]
  have : (n : ℝ) = ((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ) * (e : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hnq
    simpa using this
  rwa [this] at h1

private theorem norm_rt (w : InfinitePlace ℚ) (c : ℚ) : ‖(rt c : A ℚ).1 w‖ = |(c : ℝ)| := by
  have h : InfinitePlace.Completion.extensionEmbedding w ((rt c : A ℚ).1 w) = w.embedding c :=
    InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ c)
  have h2 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) ((rt c : A ℚ).1 w)
  rw [← h2, h, InfinitePlace.norm_embedding_eq, Rat.infinitePlace_apply, Rat.cast_abs]

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in

private theorem idele_le {K1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hK : IsCompact K1) (w : InfinitePlace ℚ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : IdeleGroup ℚ, ((x : A ℚ)).2 ∈ K1 → ab x ≤ M * ‖(x : A ℚ).1 w‖ := by
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) one_pos 1
  set Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : IdeleGroup ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ => (((p.1⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * p.2) '' (S ×ˢ K1)
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hQ : IsCompact Q := (hS.prod hK).image ((hi.comp continuous_fst).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  have hc : Continuous fun u : IdeleGroup ℚ => ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w‖ :=
    continuous_norm.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set b := max B 1
  have hb1 : 1 ≤ b := le_max_right _ _
  set D : ℝ := |((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ)|
  have hdK : algebraMap (𝓞 ℚ) ℚ d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hd0
  have hD : 0 < D := abs_pos.2 (by exact_mod_cast hdK)
  refine ⟨D * b, by positivity, fun x hx => ?_⟩
  have hρ : 0 < ab x := (IdeleGroup.ideleModule ℚ x).2
  set p : IdeleGroup ℚ := posIdele (ab x) hρ with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * x) : ℝ) = 1 := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * x) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ x : ℝ) := by
      simp [map_mul, map_inv]
    rw [h1, hp, ideleModule_posIdele]
    change (ab x ^ Module.finrank ℚ ℚ)⁻¹ * ab x = 1
    rw [Module.finrank_self, pow_one, inv_mul_cancel₀ hρ.ne']
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * x) with hu
  have hux : ((u⁻¹ * x : IdeleGroup ℚ) : A ℚ) = rt ((t : ℚ)⁻¹) * (p : A ℚ) := by
    have e1 : u⁻¹ * x = IdeleGroup.diagonal ℚ t⁻¹ * p := by
      rw [hu, map_inv, mul_inv, mul_inv, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [e1, Units.val_mul, IdeleGroup.coe_diagonal, Units.val_inv_eq_inv_val]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite _ hρ v
  have hmem : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((t : ℚ)⁻¹) ∈ Q := by
    refine ⟨(u, (x : A ℚ).2), ⟨ht, hx⟩, ?_⟩
    have := congrArg Prod.snd hux
    rw [Units.val_mul] at this
    change (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (x : A ℚ).2 = (rt ((t : ℚ)⁻¹) : A ℚ).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 at this
    rw [hp2, mul_one] at this
    exact this
  have hint : 1 ≤ D * |(((t : ℚ)⁻¹ : ℚ) : ℝ)| := by
    refine one_le_of_mem hd0 (inv_ne_zero t.ne_zero) ?_
    rw [map_mul]
    exact hd _ hmem
  have hub : ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w‖ ≤ b :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB u ht))).trans (le_max_left _ _)
  have hu1 : 1 ≤ b * ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖ := by
    have e : (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w * (((u : IdeleGroup ℚ) : A ℚ)).1 w = 1 :=
      congrFun (congrArg Prod.fst (Units.inv_mul u)) w
    have e2 := congrArg norm e
    rw [norm_mul, norm_one] at e2
    rw [← e2]
    exact mul_le_mul_of_nonneg_right hub (norm_nonneg _)
  have hxu : (x : A ℚ) = rt ((t : ℚ)⁻¹) * (p : A ℚ) * (u : A ℚ) := by
    rw [← hux, Units.val_mul, mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hxw : ‖(x : A ℚ).1 w‖ = |(((t : ℚ)⁻¹ : ℚ) : ℝ)| * ab x * ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖ := by
    have e : (x : A ℚ).1 w = (rt ((t : ℚ)⁻¹) : A ℚ).1 w * (((p : IdeleGroup ℚ) : A ℚ)).1 w * (((u : IdeleGroup ℚ) : A ℚ)).1 w :=
      congrFun (congrArg Prod.fst hxu) w
    rw [e, norm_mul, norm_mul, norm_rt, hp, norm_posIdele_infinite]
  rw [hxw]
  set T := |(((t : ℚ)⁻¹ : ℚ) : ℝ)|
  set U := ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖
  have h3 : 1 ≤ (D * T) * (b * U) := by
    have hU : 0 ≤ b * U := by positivity
    nlinarith
  calc ab x = ab x * 1 := (mul_one _).symm
    _ ≤ ab x * ((D * T) * (b * U)) := by gcongr
    _ = D * b * (T * ab x * U) := by ring

theorem UpperTheory.ab_le_mul_one_add_norm_of_finPart_mem_compact :
    ∀ (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (δ : ℚ), IsCompact K → ∃ L : ℝ, 0 < L ∧ ∀ (a : (A ℚ)ˣ) (ξ : Fin 4 → ℚ), qr δ ξ ≠ 0 → finPartPi (sc a ξ) ∈ K → ab a ≤ L * (1 + ‖infPartPi (sc a ξ)‖) := by
  intro K δ hK
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  set g : (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ) → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun v => v 2 ^ 2 - (rt δ : A ℚ).2 * v 3 ^ 2 - v 1 * v 0 with hgdef
  have hg : Continuous g := by
    have h0 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (0 : Fin 4)
    have h1 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : Fin 4)
    have h2 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (2 : Fin 4)
    have h3 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (3 : Fin 4)
    exact ((h2.pow 2).sub (continuous_const.mul (h3.pow 2))).sub (h1.mul h0)
  obtain ⟨M, hM0, hM⟩ := idele_le (hK.image hg) w
  have hδ : 0 ≤ |(δ : ℝ)| := abs_nonneg _
  refine ⟨M * (2 + |(δ : ℝ)|) + 1, by positivity, fun a ξ hT hfin => ?_⟩
  set x : IdeleGroup ℚ := a ^ 2 * IdeleGroup.diagonal ℚ (Units.mk0 (qr δ ξ) hT) with hxdef
  have hx : (x : A ℚ) = q4 δ (sc a ξ) := by
    rw [hxdef, Units.val_mul, Units.val_pow_eq_pow_val, IdeleGroup.coe_diagonal]
    simp only [Units.val_mk0, qr, q4, sc, map_sub, map_mul, map_pow]
    ring
  have hxf : ((x : A ℚ)).2 ∈ g '' K := ⟨finPartPi (sc a ξ), hfin, by rw [hx]; rfl⟩
  have hab : ab x = ab a ^ 2 := by
    rw [hxdef, ab_mul, ab_pow, ab_diagonal, mul_one]
  set N := ‖infPartPi (sc a ξ)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hc : ∀ i, ‖(sc a ξ i).1 w‖ ≤ N := fun i =>
    (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ w).trans
      (norm_le_pi_norm (infPartPi (sc a ξ)) i)
  have hxw : ‖(x : A ℚ).1 w‖ ≤ (2 + |(δ : ℝ)|) * N ^ 2 := by
    have e : (x : A ℚ).1 w = (sc a ξ 2).1 w ^ 2 - (rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2 -
        (sc a ξ 1).1 w * (sc a ξ 0).1 w := by
      rw [hx]
      rfl
    rw [e]
    have h1 := norm_sub_le ((sc a ξ 2).1 w ^ 2 - (rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2)
      ((sc a ξ 1).1 w * (sc a ξ 0).1 w)
    have h2 := norm_sub_le ((sc a ξ 2).1 w ^ 2) ((rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2)
    rw [norm_mul] at h1
    rw [norm_mul, norm_pow, norm_pow, norm_rt] at h2
    have p2 : ‖(sc a ξ 2).1 w‖ ^ 2 ≤ N ^ 2 := by gcongr; exact hc 2
    have p3 : ‖(sc a ξ 3).1 w‖ ^ 2 ≤ N ^ 2 := by gcongr; exact hc 3
    have p10 : ‖(sc a ξ 1).1 w‖ * ‖(sc a ξ 0).1 w‖ ≤ N * N := by
      gcongr
      · exact hc 1
      · exact hc 0
    have p3' : |(δ : ℝ)| * ‖(sc a ξ 3).1 w‖ ^ 2 ≤ |(δ : ℝ)| * N ^ 2 := by gcongr
    nlinarith
  have hsq : ab a ^ 2 ≤ ((M * (2 + |(δ : ℝ)|) + 1) * (1 + N)) ^ 2 := by
    have h1 := hM x hxf
    rw [hab] at h1
    have h2 : M * ‖(x : A ℚ).1 w‖ ≤ M * ((2 + |(δ : ℝ)|) * N ^ 2) := by gcongr
    set P := M * (2 + |(δ : ℝ)|) with hP
    have hP0 : 0 ≤ P := by positivity
    have h3 : P * N ^ 2 ≤ ((P + 1) * (1 + N)) ^ 2 := by
      have : N ^ 2 ≤ (1 + N) ^ 2 := by nlinarith
      have h4 : P ≤ (P + 1) ^ 2 := by nlinarith
      calc P * N ^ 2 ≤ (P + 1) ^ 2 * (1 + N) ^ 2 := by gcongr
        _ = _ := by ring
    calc ab a ^ 2 ≤ M * ((2 + |(δ : ℝ)|) * N ^ 2) := h1.trans h2
      _ = P * N ^ 2 := by rw [hP]; ring
      _ ≤ _ := h3
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
