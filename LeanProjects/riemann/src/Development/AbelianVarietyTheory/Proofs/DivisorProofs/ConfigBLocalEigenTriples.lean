import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLineScalarCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTriplePeriodIdentityCaseBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleLocalPartCaseBSecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.InfB

theorem coneFun_mul_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, l (locOpInf (om₁' (g₀, 1)) f) = l f) →
      ∀ f, ∀ p ∈ UAt σ G.V' (evI F), ∀ g ∈ UAt σ G.V' (evI F), ∀ t : (AE F E)ˣ,
        mat p *ᵥ incV F H.x = t.1 • incV F H.x →
        GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f (p * g) =
          (((absE F E t : ℝ) ^ (b + 1) : ℝ) : ℂ) *
            GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f g := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ μ hμ l hl f p hp g hg t ht
  obtain ⟨htI, n, m, g₀, hn, hnI, hlev, hmI, hg₀, rfl⟩ := GlobalTheory.T.parabolic_line_scalar_character F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ p hp t ht
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI := hμ
  have hnm : n * m ∈ UAt σ G.V' (evI F) := (UAtSub σ G.V' (evI F)).mul_mem hnI hmI
  set F₀ := locOpInf (om' (g, 1)) f with hF₀
  let h' : idelesAt E (evI F) → ℂ := fun y => (X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) *
    l (ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' (t * y.1)))) F₀))
  let c : ℂ := (X.ν t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)
  have hint : ∀ y : idelesAt E (evI F),
      l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f (n * m * g) y.1) =
        fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t * h' y := by
    intro y
    simp only [coneInfInt, map_smul, smul_eq_mul, h']
    rw [GlobalTheory.T.local_weil_operator_mul hP F E σ B a (b + 2) G X om om' hT _ hnm g hg, GlobalTheory.T.local_weil_operator_mul hP F E σ B a (b + 2) G X om om' hT n hnI m hmI,
      GlobalTheory.T.theta_triple_local_part_case_b_second hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ n hn hnI,
      GlobalTheory.T.theta_triple_period_identity_case_b hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ t g₀ m hlev hmI hg₀,
      map_smul, smul_eq_mul, hl g₀ hg₀]
    ring
  have hsh : ∀ y : idelesAt E (evI F),
      l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f g ((⟨t, htI⟩ : idelesAt E (evI F)) * y).1) =
        c * h' y := by
    intro y
    simp only [coneInfInt, map_smul, smul_eq_mul, h', c, Subgroup.coe_mul, map_mul, Circle.coe_mul, NNReal.coe_mul,
      Complex.ofReal_mul, mul_pow]
    ring
  have hfac : fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t = c * (((absE F E t : ℝ) ^ (b + 1) : ℝ) : ℂ) := by
    obtain ⟨r, hr⟩ := hT.geo.even
    have hlt := hT.geo.lt
    have hN : a + (b + 2) = 2 * (b + 1 + ((a - (b + 2)) / 2 + 1)) := by omega
    have hd : (((a + (b + 2) : ℕ) : ℝ) / 2) = ((b + 1 + ((a - (b + 2)) / 2 + 1) : ℕ) : ℝ) := by
      rw [hN]; push_cast; ring
    simp only [fac, c, hd, Real.rpow_natCast, pow_add]
    push_cast
    ring
  have key := integral_mul_left_eq_self (μ := μ)
    (fun y : idelesAt E (evI F) => l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f g y.1))
    ⟨t, htI⟩
  simp only [hsh] at key
  simp only [GlobalTheory.ThK.InfB.coneFun]
  rw [integral_congr_ae (Eventually.of_forall hint), integral_const_mul, hfac, ← key, integral_const_mul]
  ring

end GlobalTheory.ThK.InfB

end
