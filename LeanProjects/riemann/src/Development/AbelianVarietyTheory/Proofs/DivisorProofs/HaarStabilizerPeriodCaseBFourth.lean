import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeMidsetIsotropicVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorReductionTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBReducedTripleFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBReducedTripleSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralIdeleScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIdelesHaarFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIdelesHaarSecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem jrel_of_slices {d d₁ e : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E e}
    {H' : Plane E d d₁} {H₂ : Plane E d₁ e} {emb : UA σ W₁.J → UA σ W.J} {w : UA σ W.J} {nn : AE F E → UA σ W.J}
    {T₁ : Set (UA σ W₁.J)} {κ : ℂ} {ν : @Measure (AE F E) (borel _)} {Gf : UA σ W.J → ℂ}
    {χ χ' : Chr F E} {z z' : ℂ}
    (hS : ∀ (r : (AE F E)ˣ) (φ : AE F E → ℂ), (Integrable (fun c => φ (r.1 * c)) ν ↔ Integrable φ ν) ∧
      ∫ c, φ (r.1 * c) ∂ν = ((absE F E r : ℝ) : ℂ)⁻¹ * ∫ c, φ c ∂ν)
    (hC : ∀ t m, IsLevi (W₁ := W₁) H' t 1 m → ∃ m₂ : UA σ W₁.J, IsLevi (W₁ := W₂) H₂ t 1 m₂ ∧
      ∀ (γ : UA σ W₁.J) c h, w * nn c * emb γ * (m * h) = emb m₂ * (w * nn ((t⁻¹ : (AE F E)ˣ).1 * c) * emb γ * h))
    (hG : ∀ (t t' : (AE F E)ˣ) (m m' : UA σ W₁.J), IsLevi (W₁ := W₂) H₂ t 1 m → IsLevi (W₁ := W₂) H₂ t' 1 m' → ∀ g,
        Gf (emb m' * (emb m * g)) - (χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z' * Gf (emb m * g) -
        (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * Gf (emb m' * g) +
        (χ t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ z * ((χ' t' : ℂ) * ((absE F E t' : ℝ) : ℂ) ^ z') * Gf g = 0)
    (hsum : ∀ h, Summable fun γ : T₁ => ‖∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν‖)
    (hint : ∀ h (γ : T₁), Integrable (fun c => Gf (w * nn c * emb γ.1 * h)) ν) :
    GlobalTheory.ConeSmallMid.JRel (W := W) W₁ H' χ (z + 1) χ' (z' + 1)
      (fun h => κ * ∑' γ : T₁, ∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν) := by
  intro t t' m m' hm hm' h
  obtain ⟨m₂, hm₂, hc⟩ := hC t m hm
  obtain ⟨m₂', hm₂', hc'⟩ := hC t' m' hm'
  have hsc : ∀ (u : (AE F E)ˣ) (ψ : AE F E → ℂ),
      ∫ c, ψ ((u⁻¹ : (AE F E)ˣ).1 * c) ∂ν = ((absE F E u : ℝ) : ℂ) * ∫ c, ψ c ∂ν := by
    intro u ψ
    rw [(hS u⁻¹ ψ).2, map_inv, NNReal.coe_inv, Complex.ofReal_inv, inv_inv]
  have hsi : ∀ (u : (AE F E)ˣ) (ψ : AE F E → ℂ), Integrable (fun c => ψ ((u⁻¹ : (AE F E)ˣ).1 * c)) ν → Integrable ψ ν :=
    fun u ψ hi => (hS u⁻¹ ψ).1.1 hi
  set A : ℂ := ((absE F E t : ℝ) : ℂ) with hAdef
  set A' : ℂ := ((absE F E t' : ℝ) : ℂ) with hA'def
  have hA0 : A ≠ 0 := by
    rw [hAdef]; exact_mod_cast ((Group.isUnit t).map (absE F E)).ne_zero
  have hA'0 : A' ≠ 0 := by
    rw [hA'def]; exact_mod_cast ((Group.isUnit t').map (absE F E)).ne_zero
  set P : ℂ := (χ t : ℂ) * A ^ z with hP
  set P' : ℂ := (χ' t' : ℂ) * A' ^ z' with hP'
  let I : UA σ W.J → T₁ → ℂ := fun k γ => ∫ c, Gf (w * nn c * emb γ.1 * k) ∂ν
  have eM : ∀ γ : T₁, I (m * h) γ = A * ∫ c, Gf (emb m₂ * (w * nn c * emb γ.1 * h)) ∂ν := by
    intro γ
    have e := hsc t (fun c => Gf (emb m₂ * (w * nn c * emb γ.1 * h)))
    rw [← e]
    exact integral_congr_ae (Filter.Eventually.of_forall fun c => congrArg Gf (hc γ.1 c h))
  have eM' : ∀ γ : T₁, I (m' * h) γ = A' * ∫ c, Gf (emb m₂' * (w * nn c * emb γ.1 * h)) ∂ν := by
    intro γ
    have e := hsc t' (fun c => Gf (emb m₂' * (w * nn c * emb γ.1 * h)))
    rw [← e]
    exact integral_congr_ae (Filter.Eventually.of_forall fun c => congrArg Gf (hc' γ.1 c h))
  have eMM : ∀ γ : T₁, I (m' * (m * h)) γ = A' * (A * ∫ c, Gf (emb m₂' * (emb m₂ * (w * nn c * emb γ.1 * h))) ∂ν) := by
    intro γ
    have e1 := hsc t' (fun c => Gf (emb m₂' * (w * nn c * emb γ.1 * (m * h))))
    have e2 := hsc t (fun c => Gf (emb m₂' * (emb m₂ * (w * nn c * emb γ.1 * h))))
    rw [← hAdef] at e2
    rw [← hA'def] at e1
    have e3 : ∫ c, Gf (emb m₂' * (emb m₂ * (w * nn ((t⁻¹ : (AE F E)ˣ).1 * c) * emb γ.1 * h))) ∂ν =
        ∫ c, Gf (emb m₂' * (w * nn c * emb γ.1 * (m * h))) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun c => by
        show Gf (emb m₂' * (emb m₂ * (w * nn ((t⁻¹ : (AE F E)ˣ).1 * c) * emb γ.1 * h))) =
          Gf (emb m₂' * (w * nn c * emb γ.1 * (m * h)))
        rw [hc γ.1 c h])
    rw [← e2, e3, ← e1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun c => congrArg Gf (hc' γ.1 c (m * h)))
  have iB : ∀ γ : T₁, Integrable (fun c => Gf (emb m₂ * (w * nn c * emb γ.1 * h))) ν := fun γ =>
    hsi t _ ((hint (m * h) γ).congr (Filter.Eventually.of_forall fun c => congrArg Gf (hc γ.1 c h)))
  have iC : ∀ γ : T₁, Integrable (fun c => Gf (emb m₂' * (w * nn c * emb γ.1 * h))) ν := fun γ =>
    hsi t' _ ((hint (m' * h) γ).congr (Filter.Eventually.of_forall fun c => congrArg Gf (hc' γ.1 c h)))
  have hAint : ∀ γ : T₁, ∫ c, Gf (emb m₂' * (emb m₂ * (w * nn c * emb γ.1 * h))) ∂ν =
      P' * ∫ c, Gf (emb m₂ * (w * nn c * emb γ.1 * h)) ∂ν + P * ∫ c, Gf (emb m₂' * (w * nn c * emb γ.1 * h)) ∂ν -
        P * P' * I h γ := by
    intro γ
    have hf : (fun c => Gf (emb m₂' * (emb m₂ * (w * nn c * emb γ.1 * h)))) = fun c =>
        P' * Gf (emb m₂ * (w * nn c * emb γ.1 * h)) + P * Gf (emb m₂' * (w * nn c * emb γ.1 * h)) -
          P * P' * Gf (w * nn c * emb γ.1 * h) := by
      funext c
      linear_combination hG t t' m₂ m₂' hm₂ hm₂' (w * nn c * emb γ.1 * h)
    have i1 : Integrable (fun c => P' * Gf (emb m₂ * (w * nn c * emb γ.1 * h)) + P * Gf (emb m₂' * (w * nn c * emb γ.1 * h))) ν :=
      ((iB γ).const_mul P').add ((iC γ).const_mul P)
    rw [hf, integral_sub i1 ((hint h γ).const_mul _),
      integral_add ((iB γ).const_mul P') ((iC γ).const_mul P), integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hpow : ∀ (x : ℂ) (y : ℂ), x ≠ 0 → x ^ (y + 1) = x ^ y * x := fun x y hx => by
    rw [Complex.cpow_add _ _ hx, Complex.cpow_one]
  have hγ : ∀ γ : T₁, I (m' * (m * h)) γ = ((χ' t' : ℂ) * A' ^ (z' + 1)) * I (m * h) γ +
      ((χ t : ℂ) * A ^ (z + 1)) * I (m' * h) γ - ((χ t : ℂ) * A ^ (z + 1)) * ((χ' t' : ℂ) * A' ^ (z' + 1)) * I h γ := by
    intro γ
    rw [eMM, eM, eM', hAint, hpow A z hA0, hpow A' z' hA'0, hP, hP']
    ring
  have hs : ∀ k, Summable (I k) := fun k => (hsum k).of_norm
  show κ * ∑' γ, I (m' * (m * h)) γ - _ * (κ * ∑' γ, I (m * h) γ) - _ * (κ * ∑' γ, I (m' * h) γ) +
    _ * (κ * ∑' γ, I h γ) = 0
  rw [tsum_congr hγ, Summable.tsum_sub (((hs _).mul_left _).add ((hs _).mul_left _)) ((hs _).mul_left _),
    Summable.tsum_add ((hs _).mul_left _) ((hs _).mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  ring

theorem jb_mid : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      ∃ c : UA σ G.W.J → ℂ, IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T)) c ∧
        GlobalTheory.ConeSmallMid.JRel G₁.W H' X.α (((b + 2 : ℕ) : ℂ) / 2) X.β (((a + 2 : ℕ) : ℂ) / 2) c ∧
        GlobalTheory.ConeSmallMid.JRel G₁.W H' X.β (((a + 2 : ℕ) : ℂ) / 2) X.α (((b + 2 : ℕ) : ℂ) / 2) c := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  by_cases hiso : ∃ z : Fin (a + b) → E, z ≠ 0 ∧ form σ G₁.W.J z z = 0
  · obtain ⟨V, V', W₁', hT', e, W₂, H₂, i₀, i₁, hH₂⟩ := GlobalTheory.T.isotropic_vector_reduction_triple hKP F E σ B a b G₁ X om₁ om₁' hT₁ hiso
    obtain ⟨emb, hemb, ⟨w, hw⟩, nn, hnn⟩ :=
      GlobalTheory.T.exists_levi_embedding_swap_shear_of_isAdapted F E σ B a b G G₁ H H' hCfg X om om' om₁ om₁' hT hT₁ V V' W₁' hT' e W₂ H₂ i₀ i₁ hH₂
    obtain ⟨s₁g, hg⟩ := GlobalTheory.T.config_b_stabilizer_ideles_haar_first hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁
      Φ' hΦ' V V' W₁' hT' e W₂ H₂ i₀ i₁ hH₂ emb hemb
    obtain ⟨s₁u, hu⟩ := GlobalTheory.T.config_b_stabilizer_ideles_haar_second hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁
      Φ' hΦ' V V' W₁' hT' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hnn
    refine ⟨max s₁g s₁u, fun T hTr s hs hLU => ?_⟩
    obtain ⟨Gf, hCT, hJ1, hJ2⟩ := hg s (lt_of_le_of_lt (le_max_left _ _) hs)
    obtain ⟨T₁, κ, ν, hν, hc, hsum, hint⟩ := hu T hTr s (lt_of_le_of_lt (le_max_right _ _) hs) hLU Gf hCT
    have hS := GlobalTheory.T.haar_integral_idele_scaling F E σ hT.base.cm ν hν
    have hC : ∀ t m, IsLevi (W₁ := G₁.W) H' t 1 m → ∃ m₂ : UA σ G₁.W.J, IsLevi (W₁ := W₂) H₂ t 1 m₂ ∧
        ∀ (γ : UA σ G₁.W.J) c h, w * nn c * emb γ * (m * h) =
          emb m₂ * (w * nn ((t⁻¹ : (AE F E)ˣ).1 * c) * emb γ * h) := by
      intro t m hm
      obtain ⟨hcomm, m₂, hm₂, hwn⟩ := GlobalTheory.T.config_b_reduced_triple_second F E σ B a b G G₁ H H' hCfg X om om' om₁ om₁' hT hT₁ V V' W₁' hT'
        e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hnn t m hm
      refine ⟨m₂, hm₂, fun γ c h => ?_⟩
      have e1 : w * nn c * emb γ * (m * h) = (w * nn c * m) * (emb γ * h) := by
        simp only [mul_assoc]
        rw [← mul_assoc (emb γ) m h, hcomm γ, mul_assoc]
      rw [e1, hwn c]
      simp only [mul_assoc]
    have hb2 : (((b + 2 : ℕ) : ℂ) / 2) = ((b : ℕ) : ℂ) / 2 + 1 := by push_cast; ring
    have ha2 : (((a + 2 : ℕ) : ℂ) / 2) = ((a : ℕ) : ℂ) / 2 + 1 := by push_cast; ring
    refine ⟨_, hc, ?_, ?_⟩
    · rw [hb2, ha2]; exact jrel_of_slices hS hC hJ1 hsum hint
    · rw [hb2, ha2]; exact jrel_of_slices hS hC hJ2 hsum hint
  · refine ⟨0, fun T hTr s _ _ => ⟨0, ?_, ?_, ?_⟩⟩
    · have hE : GlobalTheory.ConeSmallSer.midSet H'.x T = ∅ := by
        ext t
        simp only [Set.mem_empty_iff_false, iff_false]
        intro ht
        exact hiso (GlobalTheory.T.cone_midset_isotropic_vector F E σ B a b G G₁ H H' hCfg X om om' hT T hTr.1 t ht)
      intro μ' 𝓕 _ _ _ h
      rw [hE]
      simp [GlobalTheory.ConeSmallSer.partSum]
    · intro t t' m m' _ _ h
      simp
    · intro t t' m m' _ _ h
      simp

end GlobalTheory.ConeSmallMidJB

end
