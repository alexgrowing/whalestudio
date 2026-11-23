import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DiffCont

theorem polData_of_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F)) {m : ℕ}
    (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ PolData B M := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (h i).1, φ i, (h i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
  by_contra hT
  exact hv ((h i).2.2 v hT)

theorem continuous_diff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      Continuous φ' := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq _ c Φ Φ' _ hPM c₀ hc₀ φ' hφ'
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨P, P'⟩ := GlobalTheory.ThK.Check.isPair_of_isTriple hT
  have hW := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  have hW' := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P'
    (Or.inr (by rw [hq]; exact Nat.zero_min _))
  obtain ⟨T, -, m, m', f, φ, f₁, φ₁, hf, hf₁, rfl, rfl, -⟩ := hPM
  have hS : ∑ i, pure (f i) (φ i) ∈ schA F (Fin a × Fin (a + a')) :=
    GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM (polData_of_sum G.M T f φ hf)
  have hS' : ∑ j, pure (f₁ j) (φ₁ j) ∈ schA F (Fin a' × Fin (a + a')) :=
    GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM' (polData_of_sum G.M' T f₁ φ₁ hf₁)
  have hc : Continuous (G.M.I om (∑ i, pure (f i) (φ i))) :=
    GlobalTheory.ThK.SqIntCont.continuous_I G.M om hT.weil.2.2 (IsUWeilPair.isUSplitting hT.weil).pres
      (fun Ψ hΨ => (hW.1 Ψ hΨ).1) hW.2 hS
  have hc' : Continuous (G.M'.I om' (∑ j, pure (f₁ j) (φ₁ j))) :=
    GlobalTheory.ThK.SqIntCont.continuous_I G.M' om' hT.weil'.2.2 (IsUWeilPair.isUSplitting hT.weil').pres
      (fun Ψ hΨ => (hW'.1 Ψ hΨ).1) hW'.2 hS'
  let e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ G.W.J hc₀
  have he : Continuous fun x : GAd σ (c₀ • G.W.J.map σ) => e.symm x := continuous_subtype_val.subtype_mk _
  have key : φ' = fun x => G.M.I om (∑ i, pure (f i) (φ i)) (e.symm x) -
      c * G.M'.I om' (∑ j, pure (f₁ j) (φ₁ j)) (e.symm x) :=
    funext fun x => hφ' (e.symm x) x rfl
  rw [key]
  exact (hc.comp he).sub (continuous_const.mul (hc'.comp he))

end GlobalTheory.ThK.DiffCont
