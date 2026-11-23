import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleLinePolynomialActionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.MaxLie

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.RealLift Formalism.BasicNotions.TH

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_actsD_of_isTriple (hPr : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hPr hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hPr hD hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  intro γ hγ f hf
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
  exact ⟨_, mem _, h2⟩

theorem thetaSum_rho_hasDerivAt (hPr : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) (f : SInf F (Fin a × Fin (a + a')))
    (hf : f ∈ G.M.Pol B.ψ B.emb) (f₁ : SInf F (Fin a × Fin (a + a')))
    (hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) :
    HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (pure f φ))))
      (thetaSum F (G.M.co.rho B.ψ u (pure f₁ φ))) 0 :=
  GlobalTheory.T.triple_line_polynomial_action hPr F E σ B a a' G X om om' h γ hγ f hf f₁ hA φ hSB hev u

theorem exists_lineDeriv (hPr : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Ψ ∈ algD G.M B.ψ B.emb,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Ψ x) 0) ∧
      ∀ u, HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) Φ)))
        (thetaSum F (G.M.co.rho B.ψ u Ψ)) 0 := by
  have hψ : IsStd B.ψ := h.base.std
  have hM := h.geo.hM
  have hsch : ∀ p, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting h.weil).pres p Φ hΦ
  have hAD := GlobalTheory.SquareAgree.HeisDeriv.algD_le_schA G.M B.ψ B.emb hM
  have hrs : ∀ u, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.co.rho B.ψ u Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ u Φ hΦ
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_, fun u => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simp only [map_zero, GlobalTheory.SquareAgree.CoinvPass.rho_zero']
      simpa [thetaSum] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a₁ b₁ ha₁ hb₁ ha hb =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    obtain ⟨b₂, hb₂, hpb, htb⟩ := hb
    refine ⟨a₂ + b₂, add_mem ha₂ hb₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_add, Pi.add_apply]
      exact (hpa x).add (hpb x)
    · have e : (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (a₁ + b₁)))) =
          fun t => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) a₁)) +
            thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) b₁)) := by
        funext t
        rw [map_add, GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hsch _ _ (hAD ha₁)))
          (hrs u _ (hsch _ _ (hAD hb₁)))]
      rw [e, GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hAD ha₂)) (hrs u _ (hAD hb₂))]
      exact (hta u).add (htb u)
  | smul c a₁ ha₁ ha =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    refine ⟨c • a₂, Submodule.smul_mem _ c ha₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hpa x).const_mul c
    · simp only [map_smul, GlobalTheory.SquareAgree.CoinvPass.rho_smul', GlobalTheory.SquareAgree.HeisDeriv.thetaSum_smul]
      exact (hta u).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    obtain ⟨f₁, hf₁, hA⟩ := exists_actsD_of_isTriple hPr h γ hγ f hf
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, φ, hf₁, hSB, hev, rfl⟩, fun x => ?_, fun u => ?_⟩
    · exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
    · exact thetaSum_rho_hasDerivAt hPr h γ hγ f hf f₁ hA φ hSB hev u

end Gen

theorem maxLie : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _hTr hO hT Pi rf rl p p' _hm N hN τ Y hY
    ΦD hΦD Φ hD
  have hψB := hO.psi
  subst hψB
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨Ψ, hΨ, hpt, hth⟩ := exists_lineDeriv hPr hT γ hγ ΦD (hN.1 hΦD)
  have hΨN : Ψ ∈ N := hN.2.2.2 γ hγ ΦD hΦD Ψ hΨ hpt
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algA' Ψ hΨ
  refine ⟨Ψ, hΨN, Φ₁, hΦ₁, hD₁, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := cA.surjective z
  have key : (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) =
      fun t => thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (1, γ (Multiplicative.ofAdd t)) ΦD)) := by
    funext t
    have k := (hO.weilA ΦD Φ hD 1 (oneP θ X τ Y t)).2 u
    rw [GlobalTheory.LocWeilAct.conjU_one', ← hγt t] at k
    exact k.symm
  show HasDerivAt (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) (Φ₁ (cA u)) 0
  rw [key, ← hD₁.2 u]
  exact hth u

end GlobalTheory.SquareAgree.MaxLie
