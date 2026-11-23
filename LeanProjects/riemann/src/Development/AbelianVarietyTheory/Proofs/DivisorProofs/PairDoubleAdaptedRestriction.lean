import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationSeesawStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LeviModulus

theorem exists_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (hev : IsEv B M M₁ ι ι' I e) :
    ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  obtain ⟨ei, ev, hei, hloc0, hloc⟩ := hev.loc
  have hex : ∀ v : Pl F, ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem' : Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem'
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨g, hg⟩ : ∃ g, ei g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  refine ⟨pure g φ, (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφSB hstd).2, ?_⟩
  rw [hloc g φ hφSB hcof, show (fun v => ev v (φ v)) = fun v =>
    Set.indicator {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 from funext hφev]
  intro h0
  apply hg
  apply GlobalTheory.ThK.EvUniqInf.eq_of_pure_std (ei g) 0
  rw [h0]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

end GlobalTheory.ThK.LeviModulus

open GlobalTheory.ThK.LeviModulus in

theorem GlobalTheory.ThK.LeviModulus.norm_const_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (M₁ : Model σ X₁ W₁) (om₁ : Rep σ X₁ W₁) (r₁ s₁ r₁' s₁' : ℕ),
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁' →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₁ H.ι H'.ι (isoA H H') e →
    ∀ (l : (AE F E)ˣ) (g₀ : UA σ X₁.J) (m : UA σ X.J), IsLevi (W₁ := X₁) H l g₀ m →
    ∀ c : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d), e (om (m, 1) Φ) = c • om₁ (g₀, 1) (e Φ)) →
      ‖c‖ = (absE F E l : ℝ) ^ ((d₁ : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hpair H H' j₀ j₁ i₀ i₁ M₁ om₁ r₁ s₁ r₁' s₁'
    hH hH' hpair₁ e hev l g₀ m hL c hc

  obtain ⟨M₁', hM₁'⟩ := GlobalTheory.ModelEx.model_exists F E σ B hpair.base n d₁ X W₁ r s r₁' s₁' hpair.herm hpair₁.skew
  obtain ⟨om₁', hom₁'⟩ := hKP.base.weilRepresentationExists F E σ B hpair.base n d₁ X W₁ r s r₁' s₁' hpair.herm hpair₁.skew M₁' hM₁'
    χX χW hpair.hX hpair.hW hpair.resX hpair₁.resW
  have P₁' : IsPair B M₁' χX χW om₁' r s r₁' s₁' :=
    ⟨hpair.base, hpair.herm, hpair₁.skew, hM₁', hpair.hX, hpair.hW, hpair.resX, hpair₁.resW, hom₁'⟩

  obtain ⟨e₀, he₀⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hKP.base).1 F E σ B n d X W M χX χW om r s r' s' hpair d₁ X W₁ H' i₀ i₁ M₁'
    rfl hH' hM₁').1
  obtain ⟨e', he', c', hc'0, hfac⟩ := GlobalTheory.T.adapted_evaluation_seesaw hKP F E σ B n d d₁ X W W₁ M M₁' H' i₀ i₁ hH' hM₁' e₀ he₀ n₁ X₁ H j₀ j₁
    M₁ hH hpair₁.good hpair.base hpair.good ⟨r, s, r', s', hpair.herm, hpair.skew⟩ e hev
  have hL1 : IsLevi (W₁ := W₁) H' 1 1 (1 : UA σ W.J) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [mat]
  set k : ℂ := (χW l : ℂ) * (((absE F E l : ℝ) ^ ((d₁ : ℝ) / 2) : ℝ) : ℂ) with hk

  have hlaw : ∀ Φ ∈ schA F (Fin n × Fin d), e (om (m, 1) Φ) = k • om₁ (g₀, 1) (e Φ) := by
    intro Φ hΦ
    have hpres : om (m, 1) Φ ∈ schA F (Fin n × Fin d) := (hpair.weil.isUSplitting).pres _ Φ hΦ
    have h0 := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁' om₁' r₁' s₁' hH' P₁'
      e₀ he₀ m 1 1 1 hL1 1 (Subgroup.one_mem _) Φ hΦ
    have h1 : ((χX 1 : ℂ) * (((absE F E 1 : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) = 1 := by simp
    rw [mul_one, h1, one_smul] at h0
    have h2 := (GlobalTheory.T.adapted_plane_first_variable hKP.base F E σ B n d₁ X W₁ M₁' χX χW om₁' r s r₁' s₁' P₁' n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH
      hpair₁).2 e' he' 1 l g₀ m hL 1 (Subgroup.one_mem _) (e₀ Φ) (he₀.maps Φ hΦ)
    rw [one_mul] at h2
    apply smul_right_injective _ hc'0
    calc c' • e (om (m, 1) Φ) = e' (e₀ (om (m, 1) Φ)) := (hfac _ hpres).symm
      _ = e' (om₁' (m, 1) (e₀ Φ)) := by rw [h0]
      _ = k • om₁ (g₀, 1) (e' (e₀ Φ)) := h2
      _ = k • om₁ (g₀, 1) (c' • e Φ) := by rw [hfac Φ hΦ]
      _ = c' • k • om₁ (g₀, 1) (e Φ) := by rw [map_smul, smul_comm]

  obtain ⟨Φ₀, hΦ₀, hne⟩ := exists_ne_zero hpair.good hpair₁.good hev
  have hinv : ∀ x : Fn F n₁ d₁, om₁ (g₀⁻¹, 1) (om₁ (g₀, 1) x) = x := by
    intro x
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    exact congrArg (fun T : Module.End ℂ (Fn F n₁ d₁) => T x) (map_one om₁)
  have hne' : om₁ (g₀, 1) (e Φ₀) ≠ 0 := by
    intro h0
    apply hne
    rw [← hinv (e Φ₀), h0, map_zero]
  have hck : c = k := by
    have h := (hc Φ₀ hΦ₀).symm.trans (hlaw Φ₀ hΦ₀)
    rw [← sub_eq_zero, ← sub_smul] at h
    exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_right hne')
  rw [hck, hk, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
