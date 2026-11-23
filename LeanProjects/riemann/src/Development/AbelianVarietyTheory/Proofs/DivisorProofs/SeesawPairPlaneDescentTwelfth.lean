import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneFourierStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.KernelBoundOnK

open scoped Classical

theorem tsum_le_of_denom_decay (E : Type) [Field E] [NumberField E] (d : ℕ) :
    ∃ (K : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ (N : ℕ) (f : (Fin d → E) → ℝ), 1 ≤ N → (∀ w, 0 ≤ f w) →
      (∀ w, f w ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ∀ A : ℝ, (∀ w, f w * (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ A) →
        Summable f ∧ ∑' w, f w ≤ C₀ * (N : ℝ) ^ K * A := by
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin d) one_pos
  set L := GlobalTheory.WeilM.denomLattice E (Fin d) 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  refine ⟨r, ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹, tsum_nonneg fun z => inv_nonneg.2 (pow_nonneg (by positivity) _), fun M f hM hf0 hsupp B hdec => ?_⟩
  have hB : 0 ≤ B := le_trans (mul_nonneg (hf0 0) (pow_nonneg (by positivity) _)) (hdec 0)
  let S : Set (Fin d → E) := {ξ | ∀ i, ∃ o : 𝓞 E, (M : E) * ξ i = o}
  let v : (Fin d → E) → (Fin d → mixedEmbedding.mixedSpace E) := fun ξ i => mixedEmbedding E ((M : E) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding E ((M : E) * ξ i) ∈ mixedEmbedding.integerLattice E
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : E) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective E (congrFun (congrArg Subtype.val hab) i)))
  let g : L → ℝ := fun z => ((1 + ‖z‖) ^ r)⁻¹
  have hg0 : ∀ z, 0 ≤ g z := fun z => by positivity
  let G : (Fin d → E) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGsub : Summable fun ξ : S => g (j ξ) := hL.comp_injective hj
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact hGsub.mul_left _
  have hbound : ∀ ξ : Fin d → E, f ξ ≤ G ξ := by
    intro ξ
    by_cases h0 : f ξ = 0
    · rw [h0]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace E, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := GlobalTheory.RatPointSum.norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding E ((M : E) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : f ξ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hbound hGs
  refine ⟨hfs, ?_⟩
  have hGt : ∑' ξ, G ξ = B * (M : ℝ) ^ r * ∑' ξ : S, g (j ξ) := by
    rw [← tsum_subtype, ← tsum_mul_left]
    rfl
  have hcomp : ∑' ξ : S, g (j ξ) ≤ ∑' z : L, g z := tsum_comp_le_tsum_of_inj hL hg0 hj
  calc ∑' w, f w ≤ ∑' ξ, G ξ := hfs.tsum_le_tsum hbound hGs
    _ = B * (M : ℝ) ^ r * ∑' ξ : S, g (j ξ) := hGt
    _ ≤ B * (M : ℝ) ^ r * ∑' z : L, g z := mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by ring

end GlobalTheory.KernelBoundOnK

namespace GlobalTheory.KernelBoundOnK

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J,
        Summable (fun w : Fin d → E => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖) ∧
        ∑' w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ ≤ C * (ht h : ℝ) ^ k := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK hKU
  obtain ⟨Ca, ka, hA⟩ := GlobalTheory.T.pair_adapted_plane_theta_lift hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK hKU
  obtain ⟨K', C₀, hC₀, hlat⟩ := tsum_le_of_denom_decay E d
  obtain ⟨Cb, kb, hB⟩ := GlobalTheory.T.pair_adapted_plane_fourier hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV hM₁ hev Φ hΦ g K hK hKU K'
  refine ⟨C₀ * max Cb 0 * max Ca 0 ^ (K' + kb), ka * (K' + kb) + kb, fun u hu h => ?_⟩
  obtain ⟨N, hN1, hNle, hNsupp⟩ := hA u hu h
  set t : ℝ := (ht h : ℝ) with ht_def
  have ht0 : 0 ≤ t := NNReal.coe_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set A : ℝ := max Cb 0 * ((N : ℝ) * t) ^ kb with hAdef
  have hsupp : ∀ w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
    intro w hw
    refine hNsupp w fun h0 => hw ?_
    rw [h0]
    simp [thetaSum]
  have hdec : ∀ w : Fin d → E, ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ * (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K' ≤ A := by
    intro w
    by_cases h0 : ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖ = 0
    · rw [h0, zero_mul]; positivity
    · exact (hB u hu h N hN1 w (hsupp w h0)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨hs, hle⟩ := hlat N (fun w => ‖thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))))‖) hN1 (fun _ => norm_nonneg _) hsupp A hdec
  refine ⟨hs, hle.trans ?_⟩
  have hNle' : (N : ℝ) ≤ max Ca 0 * t ^ ka := hNle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht0 _))
  have hpow : (N : ℝ) ^ (K' + kb) ≤ (max Ca 0 * t ^ ka) ^ (K' + kb) := pow_le_pow_left₀ hN0 hNle' _
  have hCb : 0 ≤ max Cb 0 := le_max_right _ _
  calc C₀ * (N : ℝ) ^ K' * A = C₀ * max Cb 0 * t ^ kb * (N : ℝ) ^ (K' + kb) := by
        rw [hAdef, mul_pow, pow_add]; ring
    _ ≤ C₀ * max Cb 0 * t ^ kb * (max Ca 0 * t ^ ka) ^ (K' + kb) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C₀ * max Cb 0 * max Ca 0 ^ (K' + kb) * t ^ (ka * (K' + kb) + kb) := by
        rw [mul_pow, ← pow_mul, pow_add t]; ring

end GlobalTheory.KernelBoundOnK
