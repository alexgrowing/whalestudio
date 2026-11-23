import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.TwPartStabBeta
open GlobalTheory.RealLift GlobalTheory.KInfPol GlobalTheory.TwPartStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem kStabL_twPart_beta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      KStabL B G.M om R.p G₁.W H' (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm _
  have hB := hm.triple.base
  have hM := hm.triple.geo.hM
  have hw := hm.triple.weil
  have hlat := hm.triple.geo.hW.lat
  have hL := actsLaws F (Fin a × Fin (a + (b + 2)))
  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2))),
      (∀ f : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) f (A f)) ∧
      ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ g ∈ G.M.Pol B.ψ B.emb, R.p (A g) = T (R.p g) := by
    intro k hk
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk
    refine ⟨A, hA, descent R.p hm.real.quot.onto A fun f hf hpf => ?_⟩
    have h0 := hm.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])
    rw [h0, map_zero]
  intro k hk k₁ hk₁ hLk f hf f₁ hAct hpf
  obtain ⟨A, hA, T, hT⟩ := hop k hk
  have e₁ : f₁ = A f := (hL f f₁ (A f)).2.2.2.1 _ hAct (hA f)
  rw [e₁, hT f hf]
  revert hpf
  suffices h : twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ≤
      (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)).comap T from fun hpf => h hpf
  refine Submodule.span_le.2 ?_
  rintro x ⟨hxV, hxE⟩
  obtain ⟨g, hg, rfl⟩ := hxV
  have hgP : g ∈ G.M.Pol B.ψ B.emb := fockDeg_le_pol _ _ _ _ hg
  refine Submodule.subset_span ⟨⟨A g, fockDeg_stable hB hw hk hA _ hg, hT g hgP⟩, ?_⟩
  intro k' hk' t hLt f' hf' f₁' hAct' hpf'
  obtain ⟨A', hA', T', hT'⟩ := hop k' hk'
  have e' : f₁' = A' f' := (hL _ _ _).2.2.2.1 _ hAct' (hA' f')
  rw [e', hT' f' hf', hpf', ← hT g hgP]
  have hAgP : A g ∈ G.M.Pol B.ψ B.emb := GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk g hgP (A g) (hA g)
  have hA'gP : A' g ∈ G.M.Pol B.ψ B.emb :=
    GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k' hk' g hgP (A' g) (hA' g)
  rw [← hT' _ hAgP]
  have hcomm : k * k' = k' * k := levi_comm hlat hcfg.hH' hLk hLt
  have c1 := acts_mul hw k k' (hA g) (hA' (A g))
  have c2 := acts_mul hw k' k (hA' g) (hA (A' g))
  rw [hcomm] at c2
  have e2 : A' (A g) = A (A' g) := (hL _ _ _).2.2.2.1 _ c1 c2
  rw [e2, hT _ hA'gP, hxE k' hk' t hLt g hgP (A' g) (hA' g) rfl, map_smul, hT g hgP]

end GlobalTheory.TwPartStabBeta
