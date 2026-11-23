import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtLeOfNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ActRat
import Development.AutomorphicArithmetic.UnipotentInvariants.ExistsCompactSiegelDecompositionHeightLe
import Development.AutomorphicArithmetic.UnipotentInvariants.AbLeMulOneAddNormOfFinPartMemCompact

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem wt_nonneg' (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N : ℕ) (v : V4 ℚ) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_add_le (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N s : ℕ) (v : V4 ℚ) :
    wt K (N + s) v ≤ wt K N v := by
  unfold wt
  split_ifs
  · have h1 : (1 : ℝ) ≤ 1 + ‖infPartPi v‖ := by linarith [norm_nonneg (infPartPi v)]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (Nat.le_add_right N s))
  · exact le_rfl

private theorem wt_decay {K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)} (N s : ℕ) {v : V4 ℚ} {T L : ℝ}
    (hT : 0 < T) (hL : 0 < L) (h : finPartPi v ∈ K → T ≤ L * (1 + ‖infPartPi v‖)) :
    wt K (N + s) v ≤ (L * T⁻¹) ^ s * wt K N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos hv]
    have hp : 0 < 1 + ‖infPartPi v‖ := by linarith [norm_nonneg (infPartPi v)]
    have h1 : (1 + ‖infPartPi v‖)⁻¹ ≤ L * T⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hp]
      have := h hv
      calc (1 : ℝ) = T * T⁻¹ := (mul_inv_cancel₀ hT.ne').symm
        _ ≤ (L * (1 + ‖infPartPi v‖)) * T⁻¹ := by gcongr
        _ = L * T⁻¹ * (1 + ‖infPartPi v‖) := by ring
    rw [pow_add, mul_inv, mul_comm, ← inv_pow (1 + ‖infPartPi v‖) s]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 s) (by positivity)
  · rw [if_neg hv, if_neg hv, mul_zero]

private theorem rt_injective : Function.Injective (rt : ℚ → A ℚ) := by
  haveI : Nontrivial (A ℚ) := ⟨⟨0, 1, fun h => by
    have e : ((0 : A ℚ).1 Rat.infinitePlace) = ((1 : A ℚ).1 Rat.infinitePlace) :=
      congrArg (fun x : A ℚ => x.1 Rat.infinitePlace) h
    exact zero_ne_one e⟩⟩
  exact (algebraMap ℚ (A ℚ)).injective

private theorem rp_injective : Function.Injective (rp : (Fin 4 → ℚ) → V4 ℚ) := fun _ _ h =>
  funext fun i => rt_injective (congrFun h i)

section Act

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E}
  {ρ : GL (Fin 2) (A E) →* GL (Fin 4) (A ℚ)}

private theorem act_mul (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (h h' : GL (Fin 2) (A E)) (v : V4 ℚ) :
    D.act (h * h') v = D.act h (D.act h' v) := by
  rw [hact, hact, hact, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem act_one (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (v : V4 ℚ) : D.act 1 v = v := by
  rw [hact, map_one, Units.val_one, Matrix.one_mulVec]

private theorem act_scale (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (h : GL (Fin 2) (A E)) (x : A ℚ) (v : V4 ℚ) :
    D.act h (fun i => x * v i) = fun i => x * D.act h v i := by
  have e : (fun i => x * v i) = x • v := rfl
  rw [e, hact, hact, Matrix.mulVec_smul]
  rfl

private theorem rat_equiv (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    ∃ e : (Fin 4 → ℚ) ≃ (Fin 4 → ℚ), (∀ ξ, D.act (gl (ratS E γ))⁻¹ (rp ξ) = rp (e ξ)) ∧
      ∀ ξ, qr D.δ (e ξ) = qr D.δ ξ := by
  have h : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (ξ : Fin 4 → ℚ), ∃ ξ', D.act (gl (ratS E γ)) (rp ξ) = rp ξ' := by
    intro γ ξ
    obtain ⟨N, -, hN⟩ := actRat ℚ E D (Matrix.SpecialLinearGroup.toGL γ)
    exact ⟨_, by rw [gl_ratS]; exact hN ξ⟩
  choose f hf using h
  have hinv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) E, (gl (ratS E γ))⁻¹ = gl (ratS E γ⁻¹) := fun γ => by
    rw [map_inv, gl_inv]
  have hcomp : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) ξ, f γ (f γ⁻¹ ξ) = ξ := fun γ ξ => rp_injective (by
    rw [← hf, ← hf, ← act_mul hact, ← gl_mul, ← map_mul, mul_inv_cancel, map_one, gl_one, act_one hact])
  have hcomp' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) E) ξ, f γ⁻¹ (f γ ξ) = ξ := fun γ ξ => by
    simpa using hcomp γ⁻¹ ξ
  obtain ⟨-, -, -, hnu, -, -, -, -, -, hqi, hqr⟩ := szLaws E D
  refine ⟨⟨f γ⁻¹, f γ, hcomp γ, hcomp' γ⟩, fun ξ => ?_, fun ξ => rt_injective ?_⟩
  · rw [hinv]
    exact hf _ ξ
  · change rt (qr D.δ (f γ⁻¹ ξ)) = _
    rw [← hqr, ← hf, hqi _ (hnu _), hqr]

private theorem term_le (hact : ∀ h v, D.act h v = (ρ h).val *ᵥ v) {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)} {n : ℕ}
    {B₁ Tz : ℝ} {x y : GL (Fin 2) (A E)} {g₀ : GL (Fin 2) (A E)} {z : GL (Fin 2) (Cinf E)} {e : (Fin 4 → ℚ) → Fin 4 → ℚ}
    (hx : x = g₀ * infGL E 2 z * y) (hlin : ∀ v, wt K n ((ρ y⁻¹).val *ᵥ v) ≤ B₁ * wt K' n v)
    (hz : ∀ v, wt K' n (D.act (infGL E 2 z)⁻¹ v) ≤ Tz * wt K' n v)
    (he : ∀ ξ, D.act g₀⁻¹ (rp ξ) = rp (e ξ)) (a : (A ℚ)ˣ) (ξ : Fin 4 → ℚ) :
    (wt K n fun i => (a : A ℚ) * D.act x⁻¹ (rp ξ) i) ≤ |B₁| * (Tz * wt K' n (sc a (e ξ))) := by
  have hxi : x⁻¹ = y⁻¹ * ((infGL E 2 z)⁻¹ * g₀⁻¹) := by
    rw [hx]
    group
  have h1 : (fun i => (a : A ℚ) * D.act x⁻¹ (rp ξ) i) =
      (ρ y⁻¹).val *ᵥ D.act (infGL E 2 z)⁻¹ (sc a (e ξ)) := by
    rw [← hact, hxi, act_mul hact, act_mul hact, he]
    have e1 : sc a (e ξ) = fun i => (a : A ℚ) * rp (e ξ) i := rfl
    rw [e1, act_scale hact, act_scale hact]
  rw [h1]
  have hw1 := wt_nonneg' K' n (D.act (infGL E 2 z)⁻¹ (sc a (e ξ)))
  exact (hlin _).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hw1).trans
    (mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)))

end Act

private theorem pow_bound {C₀ C₂ H t : ℝ} (n : ℕ) (hH : 0 ≤ H) (ht : 0 < t) (h : H ≤ C₂ * t) :
    (C₀ * H ^ 2) ^ n ≤ (|C₀| * |C₂| ^ 2) ^ n * t ^ (2 * n) := by
  have e1 : H ≤ |C₂| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ht.le)
  calc (C₀ * H ^ 2) ^ n ≤ (|C₀| * H ^ 2) ^ n := by
        refine le_trans (le_abs_self _) ?_
        rw [abs_pow, abs_mul, abs_of_nonneg (pow_nonneg hH 2)]
    _ ≤ (|C₀| * (|C₂| * t) ^ 2) ^ n := by gcongr
    _ = (|C₀| * |C₂| ^ 2) ^ n * t ^ (2 * n) := by
        rw [mul_pow |C₂|, ← mul_assoc, mul_pow, pow_mul]

private theorem sum_cmp {ι : Type} {f g : ι → ℝ} {P : ι → Prop} {M M' S : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hs : Summable g) (hS : ∑' i, g i ≤ S) (h : ∀ i, f i ≤ M * g i)
    (h' : ∀ i, P i → f i ≤ M' * g i) :
    Summable f ∧ ∑' i, f i ≤ M * S ∧ ∑' i : {i // P i}, f i.1 ≤ M' * S := by
  have hfs : Summable f := Summable.of_nonneg_of_le hf h (hs.mul_left M)
  refine ⟨hfs, ?_, ?_⟩
  · calc ∑' i, f i ≤ ∑' i, M * g i := hfs.tsum_le_tsum h (hs.mul_left M)
      _ = M * ∑' i, g i := tsum_mul_left
      _ ≤ M * S := mul_le_mul_of_nonneg_left hS hM
  · have hq : Summable fun i : {i // P i} => M' * g i.1 := (hs.mul_left M').comp_injective Subtype.val_injective
    calc ∑' i : {i // P i}, f i.1 ≤ ∑' i : {i // P i}, M' * g i.1 :=
          (hfs.comp_injective Subtype.val_injective).tsum_le_tsum (fun i => h' i.1 i.2) hq
      _ ≤ ∑' i, M' * g i := Summable.tsum_subtype_le (fun i => M' * g i) {i | P i} (fun i => mul_nonneg hM' (hg i)) (hs.mul_left M')
      _ = M' * ∑' i, g i := tsum_mul_left
      _ ≤ M' * S := mul_le_mul_of_nonneg_left hS hM'

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.latSum :
    LatSum := by
  intro E _ _ _ D K C c s hK hC _ hc
  obtain ⟨ρ, hρ, hact, -⟩ := actCont ℚ E D
  obtain ⟨N, hN⟩ := wtSum ℚ
  obtain ⟨Y, C₂, hY, hred⟩ := UpperTheory.exists_compact_siegel_decomposition_height_le E c hc
  have hCmp : IsCompact ((fun p : G1 E × GL (Fin 2) (A E) => ρ (gl p.1 * p.2)⁻¹) '' (Y ×ˢ C)) :=
    (hY.prod hC).image (hρ.comp (((continuous_gl.comp continuous_fst).mul continuous_snd).inv))
  obtain ⟨K', hK', hlin⟩ := wtLin ℚ _ hCmp K hK
  obtain ⟨B₁, hB₁⟩ := hlin (N + s)
  obtain ⟨C₀, hC₀⟩ := wtAct ℚ E D
  obtain ⟨Cs, hCs⟩ := hN K' hK' c hc
  obtain ⟨L, hL, hq⟩ := UpperTheory.ab_le_mul_one_add_norm_of_finPart_mem_compact K' D.δ hK'
  refine ⟨N + s, 2 * (N + s), |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (1 + L ^ s), fun a u b k hk ha hb => ?_⟩
  obtain ⟨γ, z, w, hw, hx, hHt⟩ := hred u b hb
  obtain ⟨e, he, heq⟩ := rat_equiv hact γ
  obtain ⟨hs, ht⟩ := hCs a ha
  have haa : 0 < ab a := ab_pos a
  have hbb : 0 < ab b := ab_pos b
  have hHt0 : 0 ≤ Ht z := by unfold Ht; positivity
  have hmem : ρ (gl w * k)⁻¹ ∈ (fun p : G1 E × GL (Fin 2) (A E) => ρ (gl p.1 * p.2)⁻¹) '' (Y ×ˢ C) :=
    ⟨(w, k), ⟨hw, hk⟩, rfl⟩
  have hterm := term_le (K := K) (K' := K') (n := N + s) (y := gl w * k) hact
    (x := gl (nU u * mD b) * k) (by rw [hx, mul_assoc]) (hB₁ _ hmem) (hC₀ K' (N + s) z) he a
  set T : ℝ := |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * ab b ^ (2 * (N + s)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hle : ∀ ξ, (wt K (N + s) fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ≤
      T * wt K' (N + s) (sc a (e ξ)) := fun ξ => by
    have hw0 := wt_nonneg' K' (N + s) (sc a (e ξ))
    refine (hterm ξ).trans ?_
    rw [hT, mul_assoc |B₁|, mul_assoc |B₁|]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_bound _ hHt0 hbb hHt) hw0) (abs_nonneg _)
  have hgt : ∑' ξ, wt K' N (sc a (e ξ)) ≤ |Cs| := by
    rw [e.tsum_eq fun ξ => wt K' N (sc a ξ)]
    exact ht.trans (le_abs_self _)
  have hM' : 0 ≤ T * (L * (ab a)⁻¹) ^ s := by positivity
  obtain ⟨h1, h2, h3⟩ := sum_cmp (P := fun ξ => qr D.δ ξ ≠ 0) hT0 hM' (fun _ => wt_nonneg' _ _ _)
    (fun _ => wt_nonneg' _ _ _) (hs.comp_injective e.injective) hgt
    (fun ξ => (hle ξ).trans (mul_le_mul_of_nonneg_left (wt_add_le K' N s _) hT0))
    (fun ξ hξ => by
      have hne : qr D.δ (e ξ) ≠ 0 := by rw [heq]; exact hξ
      have h1 := wt_decay (K := K') N s (v := sc a (e ξ)) haa hL (hq a _ hne)
      calc _ ≤ T * wt K' (N + s) (sc a (e ξ)) := hle ξ
        _ ≤ T * ((L * (ab a)⁻¹) ^ s * wt K' N (sc a (e ξ))) := mul_le_mul_of_nonneg_left h1 hT0
        _ = _ := (mul_assoc _ _ _).symm)
  have hCs0 : 0 ≤ |Cs| := abs_nonneg _
  have hLs : 0 ≤ L ^ s := by positivity
  refine ⟨h1, h2.trans ?_, h3.trans ?_⟩
  · have hQ : 0 ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) := by positivity
    calc T * |Cs| = |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) * 1 := by rw [hT]; ring
      _ ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * ab b ^ (2 * (N + s)) * (1 + L ^ s) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
      _ = _ := by ring
  · have hQ : 0 ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) := by positivity
    calc T * (L * (ab a)⁻¹) ^ s * |Cs| =
          |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) * L ^ s := by
            rw [hT, mul_pow]; ring
      _ ≤ |B₁| * (|C₀| * |C₂| ^ 2) ^ (N + s) * |Cs| * (ab a)⁻¹ ^ s * ab b ^ (2 * (N + s)) * (1 + L ^ s) :=
          mul_le_mul_of_nonneg_left (by linarith) hQ
      _ = _ := by ring
