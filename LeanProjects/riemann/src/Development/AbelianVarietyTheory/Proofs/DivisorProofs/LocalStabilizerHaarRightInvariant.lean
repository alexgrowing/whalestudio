import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesIsotropicVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerHaarQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerHaarQuotientSecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.QUnimod

theorem stabAt_isMulRightInvariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ μ : Measure (stabAt σ G.V (evFin F v) H.x), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v μ hμ
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  refine ⟨fun q => ?_⟩
  obtain ⟨u, hu, huv, g₀, g, hL, hgv, hg₀v, hq⟩ :=
    GlobalTheory.T.stabilizer_fixes_isotropic_vector F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v q.1.1 q.1.2 q.2
  have hgx : mat g *ᵥ incV F H.x = incV F H.x := by
    rw [hL.1, Units.val_one, one_smul]
  let qg : stabAt σ G.V (evFin F v) H.x := ⟨⟨g, hgv⟩, hgx⟩
  let qu : stabAt σ G.V (evFin F v) H.x := q * qg⁻¹
  have hqu : qu.1.1 = u := by
    show q.1.1 * g⁻¹ = u
    rw [hq, mul_inv_cancel_right]
  have e : q = qu * qg := by simp [qu]
  have h1 := GlobalTheory.T.local_stabilizer_haar_quotient F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v μ hμ qu (hqu ▸ hu)
  have h2 := GlobalTheory.T.local_stabilizer_haar_quotient_second F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v μ hμ qg ⟨g₀, hL, hg₀v⟩
  rw [e, show (fun x : stabAt σ G.V (evFin F v) H.x => x * (qu * qg)) = (fun x => x * qg) ∘ (fun x => x * qu) from
    funext fun x => (mul_assoc _ _ _).symm, ← Measure.map_map (measurable_mul_const _) (measurable_mul_const _), h1, h2]

end GlobalTheory.ThK.LemF.QuotInv.QUnimod

end
