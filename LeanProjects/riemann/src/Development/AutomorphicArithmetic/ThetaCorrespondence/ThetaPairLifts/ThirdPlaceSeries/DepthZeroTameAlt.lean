import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabelsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
theorem conjDualParamF_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (κ : w.adicCompletion D.host.E ≃+* w'.adicCompletion D.host.E), Continuous κ →
    (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)))
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w'.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
    (∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a)) →
    Good (GlobalTheory.LocLanglands.cls σ) →
    ∃ (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
      GlobalTheory.WeilDeligne.WD.mk b = (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)).lpDual ∧
      GlobalTheory.WeilDeligne.WD.mk b' = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocLanglands.cls σ') ∧
      b.N = b'.N ∧ ∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ' := by
  intro hL D w w' c hc hA κ hκ hκE n σ σ' e he hg
  let π₁ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose n),
      fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose n),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose n g⟩) σ.irr⟩
  have ha : GlobalTheory.PRep.IsAdmissible σ.ρ := (UpperTheory.Zero.LLC.Pr.bz _).1 (Fin n) σ.V σ.ρ σ.smooth σ.irr
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irr
  have hr := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  obtain ⟨b, b', h1, h2, h3, h4⟩ := _root_.UpperTheory.One.M.New.field hL hr
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')) c (D.host.conj : D.host.E →+* D.host.E) κ
    (fun z => (hA z).symm) hc hκ hκE n π₁ σ' e he (good_contra σ π₁ hE hg)
  first | (have hOpn := UpperTheory.One.M.opn _ (hr); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hr
  exact ⟨b, b', h1.trans (_root_.UpperTheory.One.M.LawsM.dual H n σ π₁ hg hE), h2, h3, h4⟩
end UpperTheory.One.M
end
end
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ConjPlaceDual
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ConjDual D := by
  intro hPr hL D P hLab i PI k v w' hc
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  obtain ⟨c, hc1, hc2, hc3⟩ := hγ2 k v w' hc
  have hw'g : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'g, hγ3 k _ (D.naut.plGw_over k v), hγ1 k v]
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
  have hc3' : ∀ y, γ k w' (c y) = c (D.ntypes.tg k v y) := hc3
  clear hγ1 hγ2 hγ3
  generalize D.naut.plGw k v = w at hs hc hc2 ⊢
  subst hs
  obtain ⟨hsw', -⟩ := GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w' (conjPl_symm D hc)
  subst hsw'
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i PI) s
  obtain ⟨κ, σ', e, hκ, hκc, hσ', he⟩ := GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose D D.R.nV (P.H.av.rep i PI) s σ hσ
  have hloc : ∀ w, D.naut.locV i PI w = D.nbc.locAU (D.nd.j i)
      (P.H.au.cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI)) w := fun w =>
    by rw [D.nbc.embAV_loc, P.H.emb]
  have hA := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) s σ hσ
  have hA' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) _ σ' hσ'
  rw [← hloc] at hA hA'
  obtain ⟨b, b', hb, hb', hN, hρ⟩ := _root_.UpperTheory.One.M.conjDualParamF_alt hL D s.w (GlobalTheory.TypeTame.conjSP s).w c hc1 hc2 κ hκ hκc D.R.nV σ σ' e he
    (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i PI s σ hσ)
  rw [← hA] at hb
  rw [← hA'] at hb'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.weilDeligneDualTransport_monodromy_dim_wild D _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ
  have h4 := GlobalTheory.T.weilDeligneLabel_transportDual_inverseRoots D k _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ _ _ hc3'
  refine ⟨fun hm => (P.T.mono0 _ _).2 (h1 ((P.T.mono0 _ _).1 hm)), fun ht σ₁ hσ₁ hw₁ => ?_, h4⟩
  rw [P.T.inePol _ _ σ₁ hσ₁, ← P.T.dim]
  refine h3 (fun σ₂ hσ₂ hw₂ => ?_) σ₁ hσ₁ hw₁
  rw [← P.T.inePol _ _ σ₂ hσ₂, P.T.dim]
  exact ht σ₂ hσ₂ hw₂
end GlobalTheory.ConjPlaceDual
end
end
end
