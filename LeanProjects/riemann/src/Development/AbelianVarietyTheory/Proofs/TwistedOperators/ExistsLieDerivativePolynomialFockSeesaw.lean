import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOneParamSubgroupGaussVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitPreservedByHeisenbergDerivativesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.OscLie

theorem exists_lie_deriv_pol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  choose T hT' using fun t : ℝ => GlobalTheory.T.exists_archOperator_unitaryW_seesaw B G X om om' hT (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ → f₀ ∈ G.M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    { carrier := {f | f ∈ G.M.Pol B.ψ B.emb ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add, SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : G.M.Pol B.ψ B.emb ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, GlobalTheory.T.weilAction_oneParamSubgroup_gaussVacuum_smooth B G X om om' hT γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h, GlobalTheory.T.smooth_weilOrbit_preserved_by_heisenbergDerivatives B G X om om' hT γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  have hex : ∀ f : G.M.Pol B.ψ B.emb, ∃ f' : SInf F (Fin a × Fin (a + a')), f' ∈ G.M.Pol B.ψ B.emb ∧
      ∀ x, HasDerivAt (fun t => T t (f : SInf F (Fin a × Fin (a + a'))) x) (f' x) 0 := fun f => by
    obtain ⟨-, -, f', hf', h⟩ := hPN f.2
    exact ⟨f', hf', h⟩
  choose d hdP hd using hex
  have huniq : ∀ (f g₁ g₂ : SInf F (Fin a × Fin (a + a'))), (∀ x, HasDerivAt (fun t => T t f x) (g₁ x) 0) →
      (∀ x, HasDerivAt (fun t => T t f x) (g₂ x) 0) → g₁ = g₂ := fun f g₁ g₂ h₁ h₂ =>
    SchwartzMap.ext fun x => (h₁ x).unique (h₂ x)
  let δ₀ : G.M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := d
      map_add' := fun f g => huniq _ _ _ (hd (f + g)) (fun x => by
        show HasDerivAt (fun t => T t ((f : SInf F (Fin a × Fin (a + a'))) + g) x) ((d f + d g) x) 0
        simp only [map_add, SchwartzMap.add_apply]
        exact (hd f x).add (hd g x))
      map_smul' := fun c f => huniq _ _ _ (hd (c • f)) (fun x => by simpa using (hd f x).const_mul c) }
  obtain ⟨δ, hδ⟩ := LinearMap.exists_extend δ₀
  have e : ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), δ f = d ⟨f, hf⟩ := fun f hf => by
    have := congrArg (fun φ => φ ⟨f, hf⟩) hδ
    exact this
  refine ⟨δ, fun f hf => ⟨by rw [e f hf]; exact hdP _, fun r hr x => ?_⟩⟩
  have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
    fun t => hT' t f r hr
  simp only [h1]
  rw [e f hf]
  exact (hd ⟨f, hf⟩ _).mul_const (r x)

end GlobalTheory.OscLie
