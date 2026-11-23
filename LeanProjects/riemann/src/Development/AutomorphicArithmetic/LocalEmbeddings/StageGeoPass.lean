import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.StageGeo.const_on_pure :
    GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : Base D.host.F D.host.E) (Γ : Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → GlobalTheory.SquareAgree.IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    IsHaarFD W₁ ν₁ 𝓕₁ → IsWeil ψ false W₁ X α (α / β) ωB →
    (∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B) →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) (c : ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb,
    ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
      (φ' : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, φ' v ∈ GlobalTheory.WeilM.SB _) → (∀ v ∉ Xc.T, φ v = Γ.M.vac v) → (∀ v ∉ Xc.T, φ' v = Γ.M'.vac v) →
    R.p f = R.p' f' → (∀ v ∈ Xc.T, Rf.p v (φ v) = Rf.p' v (φ' v)) →
    ∀ (Φ : WO W X → ℂ) (Φ' : WO W₁ X → ℂ), GlobalTheory.SquareAgree.IsDatum Γ.M ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ →
      GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') Φ' →
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) →
      thetaInt ωA ν 𝓕 Φ = c • thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hν₁ hw hstab R Rf c hM hc f hf f' hf' φ φ'
    s s' v v' hR hfin Φ Φ' hD hD' hint
  have hT := hM.triple
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hT
  obtain ⟨-, hC⟩ := hK' R Rf hM
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT.base.std
  have hstd := hT.geo.hM'.std
  obtain ⟨-, hco, hex, -⟩ := hC.1 Bs.v₁ hT.chars.good
  have hv₁ : Bs.v₁ ∉ Xc.T := hT.chars.good.1
  have hcof : ∀ᶠ w in Filter.cofinite, φ' w = Γ.M'.vac w :=
    Filter.Eventually.mono Xc.T.finite_toSet.compl_mem_cofinite fun w hw => v' w hw
  have hφstd : ∀ᶠ w in Filter.cofinite, φ' w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hcof.and hstd).mono fun w h => h.1.trans h.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor Bs.v₁ f' φ' hφstd
  obtain ⟨φo, hφo, hp⟩ := hex Bs.τ₁ (Rf.p' Bs.v₁ (φ' Bs.v₁))
  have hφoSB : φo ∈ GlobalTheory.WeilM.SB _ := hφo.1
  have hδ : φ' Bs.v₁ - φo ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' Bs.v₁ :=
    (hco _ (sub_mem (s' Bs.v₁) hφoSB)).1 (by rw [map_sub, hp, sub_self])
  have hupd : ∀ w, Function.update φ' Bs.v₁ φo w ∈ GlobalTheory.WeilM.SB _ := by
    intro w
    by_cases hw : w = Bs.v₁
    · subst hw; rw [Function.update_self]; exact hφoSB
    · rw [Function.update_of_ne hw]; exact s' w
  have hcof' : ∀ᶠ w in Filter.cofinite, Function.update φ' Bs.v₁ φo w = Γ.M'.vac w := by
    filter_upwards [hcof, Filter.eventually_cofinite_ne Bs.v₁] with w h1 hne
    rw [Function.update_of_ne hne]; exact h1
  obtain ⟨Φ₀D, eD⟩ : ∃ Φ₀D, Φ₀D = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' (Function.update φ' Bs.v₁ φo) := ⟨_, rfl⟩
  have h0a : Φ₀D ∈ GlobalTheory.SquareAgree.algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f', _, hf', hupd, hcof', eD⟩
  have h0s : Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ :=
    Submodule.subset_span ⟨f', _, hupd, hcof', by rw [Function.update_self]; exact hφo, eD⟩
  have hdiff : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' - Φ₀D ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ := by
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) (φ' Bs.v₁) r := by
      rw [hrt, Function.update_eq_self]
    rw [e1, eD, ← hrt, ← GlobalTheory.SquareAgree.CoinvPass.tens_sub']
    exact GlobalTheory.SquareAgree.CoinvPass.tens_mem_relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁ hstd hf' s' hcof hr hrt _ hδ
  have hpm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) Φ₀D := by
    refine ⟨insert Bs.v₁ Xc.T, Finset.subset_insert _ _, 1, 1, fun _ => f, fun _ => φ, fun _ => f',
      fun _ => Function.update φ' Bs.v₁ φo, fun _ => ⟨hf, s, fun w hw => v w fun h => hw (Finset.mem_insert_of_mem h)⟩,
      fun _ => ⟨hf', hupd, fun w hw => ?_⟩, by simp, by simp [eD], ?_⟩
    · beta_reduce
      rw [Function.update_of_ne fun h : w = Bs.v₁ => hw (h ▸ Finset.mem_insert_self _ _)]
      exact v' w fun h => hw (Finset.mem_insert_of_mem h)
    · rw [Fin.sum_univ_one, Fin.sum_univ_one, hR]
      congr 2
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases h : w = Bs.v₁
      · subst h
        show Rf.p Bs.v₁ (φ Bs.v₁) = Rf.p' Bs.v₁ (Function.update φ' Bs.v₁ φo Bs.v₁)
        rw [Function.update_self, hp, v _ hv₁, v' _ hv₁]
        exact (hM.fin.sph _ hv₁).1
      · show Rf.p w (φ w) = Rf.p' w (Function.update φ' Bs.v₁ φo w)
        rw [Function.update_of_ne h]
        exact hfin w ((Finset.mem_insert.1 hw).resolve_left h)
  have hm := GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hT _ _ hpm h0s
  obtain ⟨Φ₀, hΦ₀, hD0⟩ := hO.algB' Φ₀D h0a
  have hc1 : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : GlobalTheory.SquareAgree.kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [GlobalTheory.SquareAgree.kapX]
  have key : ∀ Ψ ∈ GlobalTheory.SquareAgree.CoinvPass.relD Γ.M' om' Bs.ψ Bs.emb Bs.v₁,
      ∃ Φ ∈ finRel ωB (algF ψ θ false A₁ B), GlobalTheory.SquareAgree.IsDatum Γ.M' ψ cB Ψ Φ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, Ψ₀, hΨ₀, rfl⟩ := hz
      obtain ⟨Φ₁, hΦ₁, hD1⟩ := hO.algB' Ψ₀ hΨ₀
      have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) = g :=
        (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc1 hO.JW₁).right_inv g
      have hW := hO.weilB Ψ₀ Φ₁ hD1 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc1 hO.JW₁ g) 1
      rw [hgu, hk] at hW
      exact ⟨_, Submodule.subset_span ⟨_, GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc1 hO.JW₁ Bs.v₁ g hg, Φ₁, hΦ₁,
        rfl⟩, GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD1⟩
    | zero => exact ⟨0, zero_mem _, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
    | add a b _ _ ha hb =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      obtain ⟨Φb, hb, hDb⟩ := hb
      exact ⟨Φa + Φb, add_mem ha hb, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ hDa hDb⟩
    | smul c a _ ha =>
      obtain ⟨Φa, ha, hDa⟩ := ha
      exact ⟨c • Φa, Submodule.smul_mem _ c ha, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c hDa⟩
  obtain ⟨Ψ, hΨ, hDΨ⟩ := key _ hdiff
  have hrel : Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) :=
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cB.surjective (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hD' hD0) hDΨ ▸ hΨ
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D h0s
  obtain ⟨N, C, hmod⟩ := GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hT Φ₀ Φ₀D hD0
    hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := GlobalTheory.ThetaAgreeConv.thetaInt_eq_zero_of_finRel hP hK hθ hTr hν₁ hw hstab hrel hint'
  funext h
  have e0 := congrFun h0 h
  have e1 : thetaInt ωB ν₁ 𝓕₁ Φ' h = thetaInt ωB ν₁ 𝓕₁ Φ₀ h := by
    simp only [thetaInt, hlin, _root_.Pi.zero_apply] at e0 ⊢
    rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e0
    exact sub_eq_zero.1 e0
  rw [_root_.Pi.smul_apply, e1,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (GlobalTheory.SquareAgree.kapX X e hO.JX) _ Φ hO.measW hO.domW
      (hO.theta_eq_A hD) h,
    GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) Φ₀D Φ₀
      hO.measW₁ hO.domW₁ (hO.theta_eq_B hD0) h,
    hc _ _ hm (GlobalTheory.SquareAgree.kapX X e hO.JX h), smul_eq_mul]
