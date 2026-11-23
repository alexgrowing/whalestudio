import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineActionSumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DerPol

theorem pairDer (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w) (χX χW : Chr F E) (om : Rep σ X W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) :
    ∀ γ ∈ Lines σ W, ∃ δ : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f ∈ M.Pol ψ τ,
      δ f ∈ M.Pol ψ τ ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro γ hγ
  obtain ⟨m, u, v, c, c₀, hat, hQ⟩ := GlobalTheory.T.weil_line_action_sum hP M ψ χX χW om hcm hψ hW γ hγ
  choose Du hDu using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (u i) (hat i).1
  choose Dv hDv using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (v i) (hat i).2
  have closed : ∀ w, At (evI F) w → ∀ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ w) f (D f)) → ∀ f ∈ M.Pol ψ τ, D f ∈ M.Pol ψ τ := by
    intro w hw D hD f hf
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 w hw f (hf N hN) (D f) (hD f)
  refine ⟨∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id, fun f hf => ⟨?_, ?_⟩⟩
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    exact closed _ (hat i).1 _ (hDu i) _ (closed _ (hat i).2 _ (hDv i) _ hf)
  · intro r hr x
    choose F₁ hF₁ using fun t : ℝ => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hcm hψ hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f
    have hd := hQ f (fun i => Dv i f) (fun i => Du i (Dv i f)) (fun i => hDv i f) (fun i => hDu i _) F₁ hF₁
      (fun i => evI F (x i))
    have e : (fun t => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x) =
        fun t => F₁ t (fun i => evI F (x i)) * r x := by
      funext t; rw [hF₁ t r hr]; rfl
    rw [e]
    refine (hd.mul_const (r x)).congr_deriv ?_
    show _ = ((∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) f) (fun i => evI F (x i)) * r x
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
    congr 2
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]; simp

theorem exists_lieDer_model' : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  exact pairDer hP G.M' B.ψ B.emb X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil' γ hγ

end GlobalTheory.DerPol

end
