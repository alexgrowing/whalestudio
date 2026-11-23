import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerPFin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

theorem kerPD_fin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr hO hT Pim rf rl p p' hMt v f φ hf hSB
    hvac hv
  classical
  have hψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hM := hT.geo.hM'
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [kapX]

  have halg : ∀ x ∈ SB _, tens (evFin D.host.F v) x r ∈ algD Γ.M' Bs.ψ Bs.emb := by
    intro x hx
    have hSBx : ∀ w, Function.update φ v x w ∈ SB _ := by
      intro w
      by_cases h : w = v
      · subst h; simpa using hx
      · rw [Function.update_of_ne h]; exact hSB w
    have hvacx : ∀ᶠ w in Filter.cofinite, Function.update φ v x w = Γ.M'.vac w :=
      (hvac.and (Filter.eventually_cofinite_ne v)).mono fun w hw => by rw [Function.update_of_ne hw.2]; exact hw.1
    rw [hrt]
    exact Submodule.subset_span ⟨f, _, hf, hSBx, hvacx, rfl⟩
  suffices H : ∀ x ∈ augAt om' v, tens (evFin D.host.F v) x r ∈ kerPD ψ θ A₁ B Bs Γ cB p' by
    have := H _ hv
    rwa [hrt, Function.update_eq_self] at this
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, φ₀, hφ₀, φ₁, hφ₁, hact, rfl⟩ := hz
    have hsub : tens (evFin D.host.F v) (φ₁ - φ₀) r = tens (evFin D.host.F v) φ₁ r - tens (evFin D.host.F v) φ₀ r := by
      funext y; simp only [tens, Pi.sub_apply, sub_mul]
    have hRest : Rest (evFin D.host.F v) φ₀ r := by
      refine ⟨hr, ?_⟩
      have hSB0 : ∀ w, Function.update φ v φ₀ w ∈ SB _ := by
        intro w
        by_cases h : w = v
        · subst h; simpa using hφ₀
        · rw [Function.update_of_ne h]; exact hSB w
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ hSB0 (GlobalTheory.PureFactor.update_eventually φ v φ₀ hstd)
    have hmove : om' (g, 1) (tens (evFin D.host.F v) φ₀ r) = tens (evFin D.host.F v) φ₁ r := hact r hRest
    obtain ⟨Ψ, hΨ, hD0⟩ := hO.algB' _ (halg φ₀ hφ₀)
    have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) = g :=
      (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).right_inv g
    have hg0 := GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc hO.JW₁ v g hg
    have hW := hO.weilB _ Ψ hD0 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) 1
    rw [hgu, hk, hmove] at hW
    have hDd := GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD0
    rw [hsub, mem_kerPD hψ]
    refine ⟨Submodule.sub_mem _ (halg φ₁ hφ₁) (halg φ₀ hφ₀), _, Submodule.sub_mem _ (hMt.mapB.stabM.1 _ hg0 Ψ hΨ) hΨ, hDd, ?_⟩
    rw [map_sub, hMt.mapB.invf _ hg0 Ψ hΨ, sub_self]
  | zero =>
    have : tens (evFin D.host.F v) (0 : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens (evFin D.host.F v) (a + b) r = tens (evFin D.host.F v) a r + tens (evFin D.host.F v) b r := by
      funext y; simp only [tens, Pi.add_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens (evFin D.host.F v) (c • a) r = c • tens (evFin D.host.F v) a r := by
      funext y; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ c ha

end GlobalTheory.SquareAgree.KerPFin

end
