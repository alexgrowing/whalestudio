import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementGK
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

theorem generic_elements_exist : GenericExistsK := by
  intro F σ _ _ _ _
  let inst : NormedField (Formalism.DworkPowerSeriesWeights.GK F σ) := (Formalism.DworkPowerSeriesWeights.gAbs F σ).toNormedField
  let ι : MvPolynomial σ F →+* Formalism.DworkPowerSeriesWeights.GK F σ := algebraMap _ _
  have hι : ∀ P, ‖ι P‖ = Formalism.DworkPowerSeriesWeights.gN P := fun P => Formalism.DworkPowerSeriesWeights.gAbs_algebraMap P
  have hev : ∀ P, MvPolynomial.eval₂ (ι.comp MvPolynomial.C) (fun i => ι (MvPolynomial.X i)) P = ι P :=
    Formalism.DworkPowerSeriesWeights.eval₂_ringHom_eq ι
  refine ⟨Formalism.DworkPowerSeriesWeights.GK F σ, inst, ?_, ?_, ι.comp MvPolynomial.C, fun i => ι (MvPolynomial.X i),
    ?_, ?_⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => Formalism.DworkPowerSeriesWeights.gAbs_add_le_max x y
  · exact charZero_of_injective_ringHom (ι.comp MvPolynomial.C).injective
  · intro z
    rw [RingHom.comp_apply, hι, Formalism.DworkPowerSeriesWeights.gN_C]
  · intro P
    rw [hev, hι]
    rfl

namespace EGaussK

open EGauss

theorem reduce (K₁ : Type) [NormedField K₁] [IsUltrametricDist K₁] [CharZero K₁]
    (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → K₁)
    (F : MvPowerSeries (ZV ν r0 r1) K₁) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1)
    (hp2 : 2 < p) (hn1 : ‖(p : K₁)‖ = (p : ℝ)⁻¹) (hu : ∀ s, ‖u s‖ ≤ 1)
    (hF : InClass (p : K₁) (hhS p u) F) :
    ∃ (K : Type) (_ : NormedField K), IsUltrametricDist K ∧
      ∃ (C : ℕ) (u' : ZMod (2 * ν) → K) (F' : MvPowerSeries (ZV ν r0 r1) K)
        (ξ : ZMod (2 * ν) → Fin r0 → K) (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
        (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
        (I' : ∀ c, Fin (l c) → Fin r1),
        EntryHyp p ν r0 r1 C u' F' TT ξ e l T ∧
        (∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
          ‖jetPair (entryOp ξ e l sf T I') F'‖) ∧
        alN e = alG TT colN hts ∧ capN sf = capG TT colN hts ∧ lsN l sf = lsG TT colN hts ∧
        ∀ (J : Finset (Fin r1)) (i : ℕ), 1 ≤ i →
          (∑ x : TpV ν r1, (if (x.1.val % 2 = 0 ∧ x.2 ∉ J) ∨ (x.1.val % 2 = 1 ∧ x.2 ∈ J)
              then e x else 0) +
            ∑ c, (if (sf c).val % 2 = 1 then ((univ.image (I' c)) ∩ J).card else 0)) ≤
          ∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then min (hts s c) i - ((univ.image (I s c)) ∩ J).card
            else ((univ.image (I s c)) ∩ J).card) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss⟩ :=
    generic_elements_exist K₁ (ZMod (2 * ν) × Fin r0 × Fin r0)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [← map_natCast φ, hφ, hn1]
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  obtain ⟨C, ξ, e, l, sf, T, I', hop, hξ, hT, hal, hcap, hls, hB⟩ :=
    struct TT colN hts hp I Y
  refine ⟨K, instK, hult, C, fun s => φ (u s), MvPowerSeries.map φ F, ξ, e, l, sf, T, I',
    ⟨hpp, hp2, hnp, fun s => by rw [hφ]; exact hu s, ?_, ?_, ?_, ?_⟩, ?_, hal, hcap, hls, hB⟩
  · have h := inClass_map φ hφ _ _ _ hF
    rwa [map_natCast, map_hhS] at h
  · intro s a
    obtain ⟨y, h⟩ := hξ s a
    rw [h]
    exact hY y
  · intro c i a
    obtain ⟨y, h⟩ := hT c i a
    rw [h]
    exact hY y
  · intro x hx
    have h : alN e x.1 = 0 := by
      rw [hal]
      unfold alG
      rw [if_neg hx]
    unfold alN at h
    exact (Finset.sum_eq_zero_iff.1 h) x.2 (Finset.mem_univ _)
  · intro n
    refine le_trans (le_ciSup (Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff _) n) ?_
    rw [← hgauss, ← hop]
    unfold frameJet
    rw [Formalism.DworkPowerSeriesWeights.eval₂_jetPairPoly, map_prod]
    simp only [Formalism.DworkPowerSeriesWeights.ringMap_minorProd, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    exact le_rfl

theorem norm_unif_pow {K : Type} [NormedField K] {p : ℕ} [hp : Fact p.Prime]
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K))
    (d : ℕ) : ‖ϖ ^ d‖ = (p : ℝ) ^ (-(rhoP p * d)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have h1p : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  have hN : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1p, Nat.cast_pow, Nat.cast_one]
  have hNpos : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hNne : p ^ 2 - 1 ≠ 0 := by
    intro h
    have h0 : ((p ^ 2 - 1 : ℕ) : ℝ) = 0 := by rw [h]; simp
    rw [hN] at h0
    linarith
  have key : ‖ϖ‖ = (p : ℝ) ^ (-(rhoP p)) := by
    have h1 : ‖ϖ‖ ^ (p ^ 2 - 1) = (p : ℝ)⁻¹ := by rw [← norm_pow, hϖ, hn]
    have h2 : ((p : ℝ) ^ (-(rhoP p))) ^ (p ^ 2 - 1) = (p : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, hN]
      unfold rhoP
      rw [neg_mul, one_div, inv_mul_cancel₀ hNpos.ne', Real.rpow_neg_one]
    have h3 : ‖ϖ‖ ^ (p ^ 2 - 1) = ((p : ℝ) ^ (-(rhoP p))) ^ (p ^ 2 - 1) := h1.trans h2.symm
    have hx : (0 : ℝ) ≤ (p : ℝ) ^ (-(rhoP p)) := Real.rpow_nonneg hp0.le _
    first
      | exact (pow_left_inj₀ (norm_nonneg _) hx hNne).1 h3
      | exact (pow_left_inj (norm_nonneg _) hx hNne).1 h3
  rw [norm_pow, key, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  congr 1
  ring

theorem descend {K : Type} [NormedField K] {p : ℕ} [hp : Fact p.Prime]
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K))
    (d : ℕ) (g : ℝ) (x y : K) (hxy : x = ϖ ^ d * y)
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(g + rhoP p * d))) : ‖y‖ ≤ (p : ℝ) ^ (-g) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [hxy, norm_mul, norm_unif_pow hn hϖ d] at hx
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(rhoP p * d)) := Real.rpow_pos_of_pos hp0 _
  have hsplit : (p : ℝ) ^ (-(g + rhoP p * d)) = (p : ℝ) ^ (-(rhoP p * d)) * (p : ℝ) ^ (-g) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  rw [hsplit] at hx
  exact le_of_mul_le_mul_left hx hpos

end EGaussK

open EGaussK DeterminantJetScaling ScaledSeriesSubstitution

theorem gauss_a_one_generic_of_entry (hE : EntryExcessBound) : GaussBoundNoOperatorGeneric := by
  intro K _ _ _ p _ ν r0 r1 _ u F TT colN hts hp I hp2 hn hu hF n
  obtain ⟨K', iK, hU, C, u', F', ξ, e, l, sf, T, I', hH, hb, hal, hcap, hls, -⟩ :=
    EGaussK.reduce K p ν r0 r1 u F TT colN hts hp I hp2 hn hu hF
  have h1 := hE K' p ν r0 r1 C u' F' TT ξ e l sf T I' hH
  rw [hal, hcap, hls] at h1
  exact (hb n).trans h1

theorem gauss_a_two_generic_of_entry (hE : EntryCappedBound) : GaussBoundArbitraryGeneric := by
  intro K _ _ _ p _ ν r0 r1 _ u F TT colN hts hp I hp2 hn hu hF n
  obtain ⟨K', iK, hU, C, u', F', ξ, e, l, sf, T, I', hH, hb, hal, hcap, hls, -⟩ :=
    EGaussK.reduce K p ν r0 r1 u F TT colN hts hp I hp2 hn hu hF
  have h1 := hE K' p ν r0 r1 C u' F' TT ξ e l sf T I' hH
  rw [hal, hcap, hls] at h1
  exact (hb n).trans h1

theorem GaussBK_of (hE : EntryB) : GaussBK := by
  intro K _ _ _ p _ ν r0 r1 i _ u F TT colN hts hp I hp2 hn hi hu hF n
  obtain ⟨K', iK, hU, C, u', F', ξ, e, l, sf, T, I', hH, hb, hal, hcap, hls, hJ⟩ :=
    EGaussK.reduce K p ν r0 r1 u F TT colN hts hp I hp2 hn hu hF
  have h1 := hE K' p ν r0 r1 C u' F' TT ξ e l sf T I'
    (univ.filter (fun b : Fin r1 => b.val < i)) hH
  rw [hal, hcap, hls] at h1
  have h2 := hJ (univ.filter (fun b : Fin r1 => b.val < i)) i hi
  have hn' : ‖(p : K')‖ = (p : ℝ)⁻¹ := hH.2.2.1
  rw [norm_mul, norm_pow, hn'] at h1
  rw [norm_mul, norm_pow, hn]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    first
      | exact inv_le_one_of_one_le₀ hp1
      | exact inv_le_one hp1
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  refine le_trans ?_ h1
  exact mul_le_mul (pow_le_pow_of_le_one hinv0 hinv h2) (hb n) (norm_nonneg _) (by positivity)

theorem gauss_a_one_generic : GaussBoundNoOperatorGeneric := gauss_a_one_generic_of_entry Top.entry_a_one

theorem gauss_a_two_generic : GaussBoundArbitraryGeneric := gauss_a_two_generic_of_entry Top.entry_a_two

theorem gauss_b_generic : GaussBK := GaussBK_of Top.entryB

theorem kernel_a_one_generic_of_gauss (h : GaussBoundNoOperatorGeneric) : KernelValuationBoundUltrametric := by
  intro K _ _ _ p _ ν r0 r1 _ u ϖ Th TT colN hts hp I h2 hn hϖ hu hF n
  have hb := h K p ν r0 r1 u _ TT colN hts hp I h2 hn hu hF n
  rw [deg_eq] at hb
  refine EGaussK.descend hn hϖ _ _ _ _ ?_ hb
  rw [frameJet_scale, MvPolynomial.coeff_C_mul]

theorem kernel_a_two_generic_of_gauss (h : GaussBoundArbitraryGeneric) : KernelBoundArbitrarySizes := by
  intro K _ _ _ p _ ν r0 r1 _ u ϖ Th TT colN hts hp I h2 hn hϖ hu hF n
  have hb := h K p ν r0 r1 u _ TT colN hts hp I h2 hn hu hF n
  rw [deg_eq] at hb
  refine EGaussK.descend hn hϖ _ _ _ _ ?_ hb
  rw [frameJet_scale, MvPolynomial.coeff_C_mul]

theorem KernelBK_of (h : GaussBK) : KernelBK := by
  intro K _ _ _ p _ ν r0 r1 i _ u ϖ Th TT colN hts hp I h2 hn hi hϖ hu hF n
  have hb := h K p ν r0 r1 i u _ TT colN hts hp I h2 hn hi hu hF n
  rw [deg_eq] at hb
  refine EGaussK.descend hn hϖ _ _ _ _ ?_ hb
  rw [frameJet_scale, MvPolynomial.coeff_C_mul, mul_left_comm]

theorem kernel_a_one_generic : KernelValuationBoundUltrametric := by
  exact kernel_a_one_generic_of_gauss gauss_a_one_generic

theorem kernel_a_two_generic : KernelBoundArbitrarySizes := by
  exact kernel_a_two_generic_of_gauss gauss_a_two_generic

theorem kernel_b_generic : KernelBK := by
  exact KernelBK_of gauss_b_generic

theorem kernel_bounds_generic_of_uniform (hS : ThmSUniform) (h1 : KernelValuationBoundUltrametric) (h2 : KernelBoundArbitrarySizes) (h3 : KernelBK) :
    KernelBoundsGeneric := by
  intro p _ K0 _ _ _ _ σ hU hζ F hF be hbe K _ _ _ j ν r0 r1 _ hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0
    hΦ0 hΦ TT colN hts hp I n
  obtain ⟨c, hc, -, -, hcl⟩ := hS K0 p σ hU hζ F hF be hbe
  have hin := hcl K j ν r0 r1 hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  have hp2 : 2 < p := hU.2.1
  have hn : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [← map_natCast j, hj, hU.2.2.1]
  have hpC : (p : K) ≠ 0 := by exact_mod_cast hU.1.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply hpC
    rw [← hϖ, zero_pow]
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2.le 2
    omega
  have hu : ∀ s : ZMod (2 * ν), ‖uS (j c) (j (σ c)) s‖ ≤ 1 := by
    intro s
    unfold uS
    split_ifs
    · rw [norm_neg, hj]
      exact norm_lift_le_one hU hc
    · rw [hj]
      exact hc
  have hin' : InClass (p : K) (hhS p (uS (j c) (j (σ c)))) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K))
      (thetaLog om oms ϖ μ (mvExp (-Φ) * U0))) := by
    unfold thetaLog
    rw [scale_scale hϖ0]
    exact hin
  exact ⟨h1 K p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hn hϖ hu hin' n,
    h2 K p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hn hϖ hu hin' n,
    fun i hi => h3 K p ν r0 r1 i _ ϖ _ TT colN hts hp I hp2 hn hi hϖ hu hin' n⟩

theorem kernel_bounds_generic : KernelBoundsGeneric := by
  exact kernel_bounds_generic_of_uniform theorem_s_uniform kernel_a_one_generic kernel_a_two_generic kernel_b_generic

end Formalism.InvariantFactorPaths.G7
