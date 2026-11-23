import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.StabLieAdelic

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.mp hΦ
  have hg' : ∀ i, ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ (g i : (Fin n × Fin d → AF F) → ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ :=
    fun i => (g i).2
  choose f φ hf hSB hvac hpure using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem _ (hf i), hSB i, hvac i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpure i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.SquareAgree.StabLieAdelic

open GlobalTheory.SquareAgree.StabLieAdelic in

theorem GlobalTheory.SquareAgree.StabLieAdelic.stabLie_adelic : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N', ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ →
    ∃ ΨD ∈ N', ∃ Φ₁ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΨD Φ₁ ∧ IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₁ := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _hTr hO hT Pi rf rl p p' _hMa N' hN
    τ Y hY ΦD hΦD Φ₀ hD
  have hψ := hO.psi
  subst hψ

  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX

  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_line_operator_polynomial hPr Bs Γ Xc om om' hT γ hγ

  obtain ⟨m, f, φ, hfφ, hΦ⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb (hN.le hΦD)
  have hΨalg : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) ∈ algD Γ.M' Bs.ψ Bs.emb :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨δ (f i), φ i, (hδ (f i) (hfφ i).1).1, (hfφ i).2.1, (hfφ i).2.2, rfl⟩

  have hpt : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) ΦD x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hδ (f i) (hfφ i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hfφ i).2.1
        (((hfφ i).2.2.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)) x
    have hfun : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) ΦD x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      rw [hΦ, map_sum, Finset.sum_apply]
    rw [hfun, Finset.sum_apply]
    exact hsum
  have hΨN := hN.stabLie γ hγ ΦD hΦD _ hΨalg hpt
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' _ hΨalg
  refine ⟨_, hΨN, Φ₁, hΦ₁, hD₁, fun z => ?_⟩

  have h1 : ∀ t : ℝ, ωB (1, oneP θ X τ Y t) Φ₀ z = GlobalTheory.WeilM.thetaSum D.host.F
      (Γ.M'.co.rho Bs.ψ (cB.symm z) (om' (1, γ (Multiplicative.ofAdd t)) ΦD)) := by
    intro t
    have h := (hO.weilB ΦD Φ₀ hD 1 (oneP θ X τ Y t)).2 (cB.symm z)
    rw [conjU_one, ← hγt t, AddEquiv.apply_symm_apply] at h
    exact h.symm
  have h2 : Φ₁ z = GlobalTheory.WeilM.thetaSum D.host.F
      (Γ.M'.co.rho Bs.ψ (cB.symm z) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i))) := by
    rw [hD₁.2 (cB.symm z), AddEquiv.apply_symm_apply]
  show HasDerivAt (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ₀ z) (Φ₁ z) 0
  rw [funext h1, h2, hΦ]
  exact GlobalTheory.T.weil_model_standard_character hPr Γ.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hT.base.std hT.geo.hM' hT.weil' γ hγ m f
    (fun i => δ (f i)) φ (fun i => ⟨(hfφ i).2.1, (hfφ i).2.2⟩) (fun i => (hδ (f i) (hfφ i).1).2) (cB.symm z)

end
