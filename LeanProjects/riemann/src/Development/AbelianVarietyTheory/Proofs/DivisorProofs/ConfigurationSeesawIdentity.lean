import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartPreservedByEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftRecursionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem frobInf_twPart_le_lowPartInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ φ : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ →
        ∀ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ x ∈ lowPartInf B G₁.M R₁.p := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ hφ x hx
  obtain ⟨s, hsub, hs⟩ := GlobalTheory.T.config_a_theta_lift_recursion hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨y, hy, rfl⟩ := hsub hx
  have hT : KEqOn B G₁.M om₁ R₁.p (lowPartInf B G₁.M R₁.p) (φ ∘ₗ s) := by
    intro k₁ hk₁ g hg g₁ hg₁ hgl h hh h₁ hh₁ hTe
    obtain ⟨k, hk, hL⟩ := GlobalTheory.T.levi_lift_maximal_compact F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hM.triple.base.cm
      hM.triple.geo.hW hC.hH' k₁ hk₁
    obtain ⟨f, hf, hfe⟩ : ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = s (R₁.p g) := by
      have hmem : s (R₁.p g) ∈ (G.M.Pol B.ψ B.emb).map R.p := by
        rw [hM.real.quot.onto]; trivial
      obtain ⟨f, hf, e⟩ := hmem
      exact ⟨f, hf, e⟩
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hM.triple.base
      hM.triple.geo.hM hM.triple.weil k hk
    have h1 := hs k₁ hk₁ k hk hL g hg g₁ hg₁ hgl f hf (A f) (hA f) hfe.symm
    have h2 := hφ.cpt k hk 1 k₁ hL hk₁ f hf (A f) (hA f) h hh h₁ hh₁ (by rw [hfe]; exact hTe)
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
    simp
  exact GlobalTheory.T.lowPart_preserved_by_equivariant hKP F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁ (φ ∘ₗ s) hT y hy

end GlobalTheory.IndLine
