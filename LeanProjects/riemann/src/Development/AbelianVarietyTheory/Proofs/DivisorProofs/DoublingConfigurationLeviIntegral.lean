import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerEvaluationThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFiniteStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.XTermConv

theorem conv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (m l g₀ * k.1, h) Φ)))‖ₑ *
        ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK < ⊤ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ m hm e he X om om' om₁ om₁' hT hT₁ Φ hΦ h

  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hμKfin : μK Set.univ < ⊤ := isCompact_univ.measure_lt_top

  have hab : a' + 2 ≤ b := by have := hT.geo.eBig; omega
  set s : ℝ := ((b : ℝ) + 2 - a') / 2 with hs_def
  have hs : 1 < s := by
    have : ((a' : ℝ) + 2) ≤ b := by exact_mod_cast hab
    rw [hs_def]; linarith
  obtain ⟨U, hU, hN⟩ := GlobalTheory.T.config_a_stabilizer_evaluation_theta hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  obtain ⟨N, hN'⟩ := GlobalTheory.T.lintegral_idele_majorant_finite F E μ hμ s hs U hU
  obtain ⟨C, hCt, hCb⟩ := hN N

  have key : ∀ (k : K) (l : (AE F E)ˣ), ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (m l g₀ * k.1, h) Φ)))‖ₑ *
        ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ≤
      C * (GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s))) := by
    intro k l
    have hA : 0 < (absE F E l : ℝ) := by
      have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h2 : absE F E l ≠ 0 := fun h0 => by simp [h0] at h1
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h2)
    have hpt : ∀ g₀, ‖thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (m l g₀ * k.1, h) Φ)))‖ₑ *
        ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) =
        ‖thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k.1, h) Φ))))‖ₑ *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := by
      intro g₀
      rw [GlobalTheory.T.doubling_eigen_intertwiner_unramified hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h l g₀ (m l g₀) (hm l g₀) k.1]
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      rw [norm_mul, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hA.le _), mul_comm (_ ^ _) ‖_‖, mul_assoc, ← Real.rpow_add hA]
      congr 2
      rw [hs_def]; push_cast; ring
    calc _ = ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k.1, h) Φ))))‖ₑ *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂G₁.M.μ := lintegral_congr fun g₀ => hpt g₀
      _ = (∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l⁻¹) (om (k.1, h) Φ))))‖ₑ ∂G₁.M.μ) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (C * GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E)) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) := by
          gcongr; exact hCb k.1 k.2 l⁻¹
      _ = _ := mul_assoc _ _ _
  calc _ ≤ ∫⁻ k : K, ∫⁻ l, C * (GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s))) ∂μ ∂μK := lintegral_mono fun k => lintegral_mono fun l => key k l
    _ = ∫⁻ k : K, C * ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ ∂μK := by
        congr 1; funext k; exact lintegral_const_mul' C _ hCt
    _ = (C * ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
          ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ) * μK Set.univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCt.lt_top hN') hμKfin

end GlobalTheory.XTermConv
