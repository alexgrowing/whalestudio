import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateCompletionIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

open private hasSupport_contra from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
open private goodCusp_dualCl from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_contra {n : ℕ} (π π' : IrrRep (GL (Fin n) k)) (e : Nonempty (π'.ρ.Equiv (contra π.ρ))) (hg : Good (cls π)) :
    Good (cls π') := by
  obtain ⟨s, h1, h2⟩ := hg
  obtain ⟨φ⟩ := e
  have h3 : HasSupport π.ρ s := h1.of_equiv (equivRep π).symm
  refine ⟨s.map Zc.dualCl, ((hasSupport_contra h3).of_equiv φ.symm).of_equiv (equivRep π'), fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
  exact goodCusp_dualCl (h2 z hz)

end

theorem tw_eqG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}
    (H : Laws a ha ε rc) (x : IrrGL (w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hg : Good x) :
    rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  rw [Old.twist H x χ hχ hg, H.one, lpChar_lpOfChar]

theorem cls_eq_of_locV_eqG (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i)
    (sp : SplitPlace D.host.E) (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) (hg : Good (GlobalTheory.LocLanglands.cls σ')) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' := by
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hσ
  have h3' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q') sp σ' hσ'
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w] at h3
  rw [← P.H.emb i Q', ← D.nbc.embAV_loc i Q' sp.w] at h3'
  rw [he] at h3
  obtain ⟨a, ha, ε, -, hlaws⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)
  exact Old.inj hlaws _ _ hg (h3.symm.trans h3')

theorem conjDualParamG : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (κ : w.adicCompletion D.host.E ≃+* w'.adicCompletion D.host.E), Continuous κ →
    (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)))
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w'.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
    (∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a)) →
    Good (GlobalTheory.LocLanglands.cls σ) →
    ∃ (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
      GlobalTheory.WeilDeligne.WD.mk b = (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)).lpDual ∧
      GlobalTheory.WeilDeligne.WD.mk b' = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w') (GlobalTheory.LocLanglands.cls σ') ∧
      b.N = b'.N ∧ ∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ' := by
  intro hP hL D w w' c hc hA κ hκ hκE n σ σ' e he hg
  let π₁ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose n),
      fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose n),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose n g⟩) σ.irr⟩
  have ha : GlobalTheory.PRep.IsAdmissible σ.ρ := (hP.bz _).1 (Fin n) σ.V σ.ρ σ.smooth σ.irr
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irr
  have hr := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)
  obtain ⟨b, b', h1, h2, h3, h4⟩ := Old.field hL hr
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w')) c (D.host.conj : D.host.E →+* D.host.E) κ
    (fun z => (hA z).symm) hc hκ hκE n π₁ σ' e he (good_contra σ π₁ hE hg)
  obtain ⟨_, _, _, -, H⟩ := hr
  exact ⟨b, b', h1.trans (Old.dual H n σ π₁ hg hE), h2, h3, h4⟩

end UpperTheory.One.M
