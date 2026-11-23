import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem rest_of_rest_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {g : SInf F κ} (hg : g ≠ 0)
    {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑g) r) (f : SInf F κ) : Rest (evI F) (⇑f) r := by
  refine ⟨hr.1, ?_⟩
  have hSB := GlobalTheory.RealLift.mem_SB_of_pureA_mem hg (GlobalTheory.RealLift.tens_eq_pureA (⇑g) hr.1 ▸ hr.2)
  rw [GlobalTheory.RealLift.tens_eq_pureA (⇑f) hr.1]
  exact Submodule.subset_span ⟨f, _, hSB, rfl⟩

theorem fixPart_kStabUp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ m : ℕ, KStabUp B om (fixPart B G.M om m) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT m k hk f hf f₁ hf₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) hT.base hT.geo.hM hT.weil k hk
  have hL := GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))
  have hcomm : ∀ k₁ : UA σ G.V.J, ∀ Φ, om (k₁, 1) (om (1, k) Φ) = om (1, k) (om (k₁, 1) Φ) := by
    intro k₁ Φ
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    exact Prod.ext (by simp) (by simp)
  have hgen : ∀ g ∈ {f | f ∈ fockDeg G.M B.ψ B.emb m ∧ IsKFix B om f},
      A g ∈ {f | f ∈ fockDeg G.M B.ψ B.emb m ∧ IsKFix B om f} := by
    rintro g ⟨hgd, hgk⟩
    refine ⟨GlobalTheory.KInfFockDeg.fockDeg_stable_kInf F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) _ _ _ _ hT.base
      hT.geo.hV hT.geo.hW hT.geo.hM hT.weil k hk m g hgd (A g) (hA g), ?_⟩
    intro k₁ hk₁ r hr
    by_cases h0 : A g = 0
    · have hz : tens (evI F) ⇑(A g) r = 0 := by
        funext x
        simp [tens, h0]
      rw [hz, map_zero]
    · have hrg : Rest (evI F) (⇑g) r := rest_of_rest_ne_zero h0 hr g
      rw [← hA g r hrg, hcomm, hgk k₁ hk₁ r hrg]
  have hle : fixPart B G.M om m ≤ (fixPart B G.M om m).comap A :=
    Submodule.span_le.2 fun g hg => Submodule.mem_comap.2 (Submodule.subset_span (hgen g hg))
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.IndLine

end
