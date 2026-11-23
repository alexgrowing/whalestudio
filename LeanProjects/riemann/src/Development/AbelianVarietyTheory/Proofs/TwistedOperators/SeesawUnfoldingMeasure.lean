import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSquareIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingGlobalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingNormalizedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingPositiveStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

theorem GlobalTheory.SquareAgree.kernel_maximal_thetaSubspace : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (algD Γ.M Bs.ψ Bs.emb) K ∧ K ≠ algD Γ.M Bs.ψ Bs.emb ∧
      (∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → K ≤ N → N = K ∨ N = algD Γ.M Bs.ψ Bs.emb) ∧
      ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (ΦD ∈ K ↔ p Φ = 0) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
  have hpsi := hO.psi
  subst hpsi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hT.base.std

  let dF : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) → (WO W X → ℂ) :=
    fun ΦD x => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm x) ΦD)
  have hdat : ∀ ΦD f, IsDatum Γ.M Bs.ψ cA ΦD f → f = dF ΦD := by
    intro ΦD f h
    funext x
    have := h.2 (cA.symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  have hdat' : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), IsDatum Γ.M Bs.ψ cA ΦD (dF ΦD) := by
    intro ΦD h
    refine ⟨h, fun u => ?_⟩
    show _ = GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm (cA u)) ΦD)
    rw [AddEquiv.symm_apply_apply]
  have hS : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)) := by
    intro ΦD h
    obtain ⟨_, _, hd⟩ := hO.algA' ΦD h
    exact hd.1
  have dF_sub : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF (ΦD - ΨD) = dF ΦD - dF ΨD := by
    intro ΦD h ΨD h'
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hstd (hdat' ΦD h) (hdat' ΨD h'))).symm
  have dF_add : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF (ΦD + ΨD) = dF ΦD + dF ΨD := by
    intro ΦD h ΨD h'
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_add hstd (hdat' ΦD h) (hdat' ΨD h'))).symm
  have dF_smul : ∀ (c : ℂ), ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      dF (c • ΦD) = c • dF ΦD := by
    intro c ΦD h
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c (hdat' ΦD h))).symm
  have dF_zero : dF 0 = 0 := (hdat _ _ GlobalTheory.SquareAgree.CoinvPass.isDatum_zero).symm
  have hAlgF : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, dF ΦD ∈ algF Bs.ψ θ true A B := by
    intro ΦD h
    obtain ⟨Φ, hΦ, hd⟩ := hO.algA' ΦD h
    rw [← hdat _ _ hd]; exact hΦ
  have inj : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF ΦD = dF ΨD → ΦD = ΨD := by
    intro ΦD h ΨD h' he
    have h0 := GlobalTheory.T.eq_zero_of_thetaDistribution_heisenbergTranslates Γ.M Bs.ψ hstd (ΦD - ΨD) (sub_mem h h') (fun u => by
      have := congrFun (dF_sub ΦD h ΨD h') (cA u)
      rw [he, sub_self] at this
      have e2 : dF (ΦD - ΨD) (cA u) = GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (ΦD - ΨD)) := by
        show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm (cA u)) (ΦD - ΨD)) = _
        rw [AddEquiv.symm_apply_apply]
      rw [← e2, this]; rfl)
    exact sub_eq_zero.1 h0
  have toS : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF ΦD ∈ algF Bs.ψ θ true A B →
      ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
    intro ΦD h hF
    obtain ⟨ΨD, hΨ, hd⟩ := hO.algA _ hF
    rw [inj ΦD h ΨD (hS _ hΨ) (hdat _ _ hd)]
    exact hΨ

  have hWf : ∀ h' ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, kapX X e hO.JX h') ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧
      dF (om (1, kapX X e hO.JX h') ΦD) = ωA (1, h') (dF ΦD) := by
    intro h' hh' ΦD hΦD
    have hd := hO.weilA ΦD (dF ΦD) (hdat' ΦD (hS _ hΦD)) 1 h'
    rw [GlobalTheory.LocWeilAct.conjU_one'] at hd
    have e1 := hdat _ _ hd
    refine ⟨toS _ hd.1 ?_, e1.symm⟩
    rw [← e1]
    exact hm.mapA.stabX.1 h' hh' _ (hAlgF _ hΦD)
  have hVf : ∀ g' ∈ GfC W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g', 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧
      dF (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g', 1) ΦD) = ωA (g', 1) (dF ΦD) := by
    intro g' hg' ΦD hΦD
    have hd := hO.weilA ΦD (dF ΦD) (hdat' ΦD (hS _ hΦD)) g' 1
    rw [GlobalTheory.KapXLine.kapX_one] at hd
    have e1 := hdat _ _ hd
    refine ⟨toS _ hd.1 ?_, e1.symm⟩
    rw [← e1]
    exact hm.mapA.stabM.1 g' hg' _ (hAlgF _ hΦD)

  let K : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
    { carrier := {ΦD | ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧ p (dF ΦD) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        rw [dF_add a (hS _ ha) b (hS _ hb), map_add, ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, by rw [dF_zero, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, ?_⟩
        rw [dF_smul c a (hS _ ha), map_smul, ha', smul_zero] }
  have memK : ∀ ΦD, ΦD ∈ K ↔ ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧ p (dF ΦD) = 0 := fun _ => Iff.rfl
  refine ⟨K, ⟨⟨fun x hx => hx.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    rintro v h hh ΦD ⟨hΦD, hp0⟩
    obtain ⟨h', hh', rfl⟩ := GlobalTheory.T.transposeGramUnitary_surjective_finitePlaceSupported D X e Γ.W hO.JX v h hh
    obtain ⟨h1, h2⟩ := hWf h' hh' ΦD hΦD
    refine ⟨h1, ?_⟩
    rw [h2, hm.mapA.eqf h' hh' _ (hAlgF _ hΦD), hp0, map_zero]
  · rintro k hk ΦD ⟨hΦD, hp0⟩
    have h1 := GlobalTheory.T.seesaw_unfolding_square_integral hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD
    exact ⟨h1, GlobalTheory.T.p_eq_zero_of_kInf_right_translate hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ h1)) hp0⟩
  · rintro γ hγ ΦD ⟨hΦD, hp0⟩ Φ₁ hΦ₁ hder
    exact ⟨hΦ₁, GlobalTheory.T.seesaw_unfolding_global_integral hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm γ hγ ΦD hΦD Φ₁ hΦ₁ hder _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ hΦ₁)) hp0⟩
  ·
    intro v g hg ΦD hΦD
    have hg' := GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W Γ.V 1 one_ne_zero hO.JW v g hg
    have eg : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (GlobalTheory.ConjUTransport.conjUInv W 1 one_ne_zero hO.JW g) = g :=
      (GlobalTheory.ConjUTransport.conjEquiv W 1 one_ne_zero hO.JW).apply_symm_apply g
    obtain ⟨h1, h2⟩ := hVf _ hg' ΦD hΦD
    rw [eg] at h1 h2
    refine ⟨sub_mem h1 hΦD, ?_⟩
    rw [dF_sub _ (hS _ h1) _ (hS _ hΦD), map_sub, h2, hm.mapA.invf _ hg' _ (hAlgF _ hΦD), sub_self]
  · intro k hk ΦD hΦD
    have h1 := GlobalTheory.T.seesaw_unfolding_compatible hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD
    refine ⟨sub_mem h1 hΦD, ?_⟩
    rw [dF_sub _ (hS _ h1) _ (hS _ hΦD), map_sub,
      GlobalTheory.T.seesaw_unfolding_inner_product hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
        Pi rf rl p p' hm k hk ΦD hΦD _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ h1)), sub_self]
  · intro γ hγ ΦD hΦD Φ₁ hΦ₁ hder
    exact ⟨hΦ₁, GlobalTheory.T.seesaw_unfolding_swap hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm γ hγ ΦD hΦD Φ₁ hΦ₁ hder _ (hdat' _ (hS _ hΦ₁))⟩
  ·
    intro hK
    have hnt := hm.irred.1
    have : ∃ Φ ∈ algF Bs.ψ θ true A B, p Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hb : (algF Bs.ψ θ true A B).map p = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨Φ, hΦ, rfl⟩
        exact (Submodule.mem_bot ℂ).2 (hc Φ hΦ)
      rw [hm.mapA.onto] at hb
      exact top_ne_bot hb
    obtain ⟨Φ, hΦ, hp⟩ := this
    obtain ⟨ΦD, hΦD, hd⟩ := hO.algA Φ hΦ
    have hK' : ΦD ∈ K := hK ▸ hΦD
    exact hp (by rw [hdat _ _ hd]; exact hK'.2)
  ·
    intro N hN hKN
    have hNS : ∀ ΦD ∈ N, ΦD ∈ algD Γ.M Bs.ψ Bs.emb := fun ΦD h => hN.1.1 h
    let NI : Submodule ℂ Pi :=
      { carrier := {y | ∃ ΦD ∈ N, p (dF ΦD) = y}
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, add_mem ha hb, by rw [dF_add a (hS _ (hNS _ ha)) b (hS _ (hNS _ hb)), map_add]⟩
        zero_mem' := ⟨0, zero_mem _, by rw [dF_zero, map_zero]⟩
        smul_mem' := by
          rintro c _ ⟨a, ha, rfl⟩
          exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [dF_smul c a (hS _ (hNS _ ha)), map_smul]⟩ }
    have hirr := hm.irred.2 NI ?_ ?_
    · rcases hirr with hb | ht
      · left
        refine le_antisymm (fun ΦD hΦD => ⟨hNS _ hΦD, ?_⟩) hKN
        have : p (dF ΦD) ∈ NI := ⟨ΦD, hΦD, rfl⟩
        rw [hb] at this
        exact (Submodule.mem_bot ℂ).1 this
      · right
        refine le_antisymm (fun ΦD h => hNS _ h) (fun ΦD hΦD => ?_)
        have : p (dF ΦD) ∈ NI := by rw [ht]; trivial
        obtain ⟨ΨD, hΨ, he⟩ := this
        have hd : ΦD - ΨD ∈ K := ⟨sub_mem hΦD (hNS _ hΨ), by
          rw [dF_sub _ (hS _ hΦD) _ (hS _ (hNS _ hΨ)), map_sub, he, sub_self]⟩
        have := add_mem (hKN hd) hΨ
        rwa [sub_add_cancel] at this
    · rintro g hg _ ⟨ΦD, hΦD, rfl⟩
      refine ⟨_, GlobalTheory.T.kapX_finite_action_mem_of_isStabW hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
        Pi rf rl p p' hm N hN.1 g hg ΦD hΦD, ?_⟩
      rw [(hWf g hg ΦD (hNS _ hΦD)).2, hm.mapA.eqf g hg _ (hAlgF _ (hNS _ hΦD))]
    · rintro τ Y hY _ ⟨ΦD, hΦD, rfl⟩
      obtain ⟨Φ₁D, hΦ₁D, Φ₁, hΦ₁, hd, hder⟩ := GlobalTheory.T.seesaw_unfolding_positive hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ
        Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm N hN.1 τ Y hY ΦD hΦD (dF ΦD) (hdat' _ (hS _ (hNS _ hΦD)))
      refine ⟨Φ₁D, hΦ₁D, ?_⟩
      rw [← hdat _ _ hd]
      exact hm.mapA.eql τ Y hY _ (hAlgF _ (hNS _ hΦD)) _ hΦ₁ hder
  ·
    intro Φ _ ΦD hΦD hd
    rw [hdat _ _ hd]
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩

end
