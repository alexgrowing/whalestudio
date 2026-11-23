import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLaurentCoeffSubConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerVan

theorem mem_aux {G : Type*} [Group G] (K : Set G) (B : Set ℝ) (c : ℝ → G) (x y m : G) (t : ℝ)
    (hk : x * m * (y * c t) ∈ K) (ht : t ∈ B) :
    m ∈ (fun p : G × ℝ => x⁻¹ * p.1 * (y * c p.2)⁻¹) '' (K ×ˢ B) :=
  ⟨(x * m * (y * c t), t), ⟨hk, ht⟩, by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]⟩

end MainStatements.WeightKernel.Dec.DDerVan

theorem MainStatements.WeightKernel.Dec.derVan : MainStatements.WeightKernel.Dec.SmOf → MainStatements.WeightKernel.Dec.DerMem → MainStatements.WeightKernel.Dec.DerVan := by
  intro hSm hDer F E _ _ _ _ _ σ h n J hJ N hN f hf b hb hV ν _ x y
  have hfc := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) hf
  have hf'c := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) (hDer F E σ h n J hJ f hf b hb)
  have hs := hSm F E σ h n J hJ f hf
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hK : IsCompact (tsupport f ∪ tsupport (lineDer b f)) := IsCompact.union hfc.2 hf'c.2
  have hS : IsCompact ((fun p : GAd σ J × ℝ => x⁻¹ * p.1 * (y * b p.2)⁻¹) ''
      ((tsupport f ∪ tsupport (lineDer b f)) ×ˢ Metric.closedBall (0 : ℝ) 1)) :=
    (hK.prod (isCompact_closedBall 0 1)).image
      ((continuous_const.mul continuous_fst).mul ((continuous_const.mul (hbc.comp continuous_snd)).inv))
  have hC := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have key := GlobalTheory.LaurentAut.hasDerivAt_integral_cpt (𝕜 := ℝ) ν (x₀ := 0)
    (Φ := fun t (m : N) => f (x * m * (y * b t))) (Φ' := fun t (m : N) => lineDer b f (x * m * (y * b t))) hC ?_ ?_ ?_ ?_
  · have h0 : (fun t : ℝ => ∫ m : N, f (x * m * (y * b t)) ∂ν) = fun _ => 0 := funext fun t => hV ν x (y * b t)
    rw [h0] at key
    have e := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa [GlobalTheory.UAut.ConstAut.realLine_zero h hb] using e
  · intro t
    exact hfc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  · exact hf'c.1.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_const.mul (hbc.comp continuous_fst)))
  · intro t ht m hm
    have hnot : x * ↑m * (y * b t) ∉ tsupport f ∪ tsupport (lineDer b f) := fun hk =>
      hm (MainStatements.WeightKernel.Dec.DDerVan.mem_aux _ _ b x y (↑m) t hk ht)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inl h')),
      image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inr h'))⟩
  · intro t m
    have := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hb (x * ↑m * y) t
    simpa [mul_assoc] using this
