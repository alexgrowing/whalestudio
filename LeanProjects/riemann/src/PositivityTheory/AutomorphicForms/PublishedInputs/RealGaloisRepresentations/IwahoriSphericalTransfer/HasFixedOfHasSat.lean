import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalGlobalCompatibilityReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.TwistUnr

section Loc

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

theorem isLocComp_twist {π : TR.CuspSub F a} {η : HChar F} (hT : IsoTwist π η) {u : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    π.IsLocComp u (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)) := by
  obtain ⟨T, hT1, -, -⟩ := hT
  obtain ⟨f, hf0, hf⟩ := hσ
  have key : ∀ g x, π.locRep u g (T.symm x) =
      ((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • T.symm (π.locRep u g x) := by
    intro g x
    have h1 := hT1 (locGL F a u g) (T.symm x)
    rw [LinearEquiv.apply_symm_apply, TR.CuspSub.chiDet_locGL] at h1
    apply T.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact h1
  refine ⟨T.symm.toLinearMap ∘ₗ f, fun h => hf0 (LinearMap.ext fun v => T.symm.injective ?_), fun g v => ?_⟩
  · have h2 := LinearMap.congr_fun h v
    rw [LinearMap.zero_apply, map_zero]
    exact h2
  · change T.symm (f (((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • σ.ρ g v)) = π.locRep u g (T.symm (f v))
    rw [key, LinearMap.map_smul, LinearEquiv.map_smul]
    congr 2
    exact hf g v

theorem hasFixed_of_hasSat (hL : LocCompR) {π : TR.CuspSub F a} {u : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ}
    (hB : π.HasSat u B) {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    HasFixed σ.ρ (GlobalTheory.LFun.KGL u a) := by
  refine ((hL F a π u).2 σ hσ).hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL u a).2 ?_
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hB.1
  exact ⟨x, h0, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk⟩

end Loc

section Par

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem unr_of_hasFixed {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w n)) :
    (rc (cls (ParLaws.toRep σ))).unr := by
  refine (ParLaws.unr_iff H _).2 ?_
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  obtain ⟨v, h0, hv⟩ := hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩

theorem ine_trivial {x : WD h} (hx : x.unr) (hd : 1 ≤ x.lpDim) {ξ : Weil h →* ℂˣ} (hξ : IsSmooth ξ)
    (ht : (x.lpChar (WD.lpOfChar h ξ hξ)).unr) (s : Ine (F := E) A) : ξ (ineIncl h s) = 1 := by
  rw [lpChar_lpOfChar] at ht
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.unr_mk] at ht
  rw [WD.unr_mk] at hx
  rw [WD.lpDim_mk] at hd
  have h1 := ht.2 s
  change ((ξ (ineIncl h s) : ℂ) • b.ρ (ineIncl h s)) = 1 at h1
  rw [hx.2 s] at h1
  have hn : 1 ≤ n := by simpa using hd
  have h3 := congrFun (LinearMap.congr_fun h1 (fun _ => 1)) ⟨0, hn⟩
  simpa using h3

end Par

end GlobalTheory.RealGal.TwistUnr

open GlobalTheory.RealGal.TwistUnr in

theorem GlobalTheory.RealGal.unrAt_of_isoTwist : GlobalTheory.Mem.LiteralAutomorphy.LitN → AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F), IsoTwist π η →
    ∀ (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ), π.HasSat u B → η.UnrAt u := by
  intro LN hA F _ _ _ a ha π η hT u B hB
  have hL := GlobalTheory.T.local_global_compatibility_real hA
  have L := LN.loc
  obtain ⟨σ, hσ⟩ := (hL F a π u).1
  have hσ' := isLocComp_twist hT hσ
  obtain ⟨A, hAu⟩ := exists_isPlaceOver (AlgebraicClosure F) u
  obtain ⟨rc, hrc⟩ := L.llc F (AlgebraicClosure F) A u hAu
  have H : IsRec hAu rc := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz
    F (AlgebraicClosure F) A u hAu rc hrc
  have u1 := unr_of_hasFixed H σ (hasFixed_of_hasSat hL hB hσ)
  have u2 := unr_of_hasFixed H _ (hasFixed_of_hasSat hL hB hσ')
  obtain ⟨ar, har, ε, -, LL⟩ := H
  have hs := GlobalTheory.HeckeComp.smooth_loc η u
  have e : rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)))) =
      (rc (cls (ParLaws.toRep σ))).lpChar (rc (.ofChar (η.loc u) hs)) := by
    rw [← LL.twist]
    exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm
  rw [e, LL.one] at u2
  have hd : 1 ≤ (rc (cls (ParLaws.toRep σ))).lpDim := by rw [LL.dim]; exact ha
  have hi := ine_trivial u1 hd _ u2
  have hU : (WD.lpOfChar hAu ((η.loc u).comp ar) (har.smooth hs)).unr := by
    rw [WD.lpOfChar, WD.unr_mk]
    refine ⟨rfl, fun s => LinearMap.ext fun v => funext fun i => ?_⟩
    have := hi s
    simp [this]
  have hU' := (GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff har hs).1 hU
  intro x hx
  refine hU' x ?_
  have h0 : Valued.v (x : u.adicCompletion F) ≠ 0 := by simp
  rw [← GlobalTheory.SmGL.ord_eq_zero_iff, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]
  unfold IsUnitAt at hx
  rw [hx, WithZero.log_one]
