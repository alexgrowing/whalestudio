import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodNotMemBadPlStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SummandEig
theorem offBad_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.T.place_below_good_not_mem_badPl
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
  obtain ⟨s, α, hov, hα, hR1, hR2⟩ := frameReps D (Formalism.IndefR.Links.Vc D j) D.R.nV hAg.hF (hAg.PV j) (hAg.stdV j) Pp hS d hd
  obtain ⟨c, hc1⟩ := irrScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s α hα _ _ _ hR1 hR2
  have hc := isoScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s.v _ _ _ c hc1
  have hsB : s.v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.SummandEig.offBad_alt hL D P X i hμ Pp hG s.v hov
  refine ⟨c, fun f' hf' g => ?_⟩
  have hFI : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have h := hf'
    rw [P.H.av.typeV i Q] at h
    exact h
  have hFT : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f') := by
    intro κ hκ ht
    have ht' : TrivOutside (Formalism.L2.badPl D i)ᶜ κ := fun v hv => ht v fun h => hv (by
      rw [Set.mem_singleton_iff.1 h]
      exact hsB)
    obtain ⟨h1, h2⟩ := P.H.hecke.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := hFT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have hkey := cast_sum P.M (D.nd.mu i) hj _ _ (by omega) (by omega) f' _ _ c (hc _ hFI hfix)
  have hreal : ∀ w, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w)) =
      (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w) := by
    intro w
    rw [hAg.real (D.nd.mu i) hμ j f' (hAg.a j * w), inv_mul_cancel_left]
  have hfin : ∀ w, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' ((hAg.PV j).ψ w * γ) =
      c • X.fn hμ j f' ((hAg.PV j).ψ w) := by
    intro w
    apply (hAg.eW (D.nd.mu i) hμ j).injective
    rw [map_sum, map_smul, hreal]
    have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w * γ)) =
        Formalism.L2.NG.rt D.host.E D.R.nV (Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
          ((P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f') (hAg.a j * w) := by
      intro γ hγ
      have e2 : (hAg.PV j).ψ w * γ = (hAg.PV j).ψ (w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ) := by
        rw [map_mul, Formalism.IndefR.principalLevelFrame.pre_spec (hAg.PV j) (rep_mem _ Pp d hγ)]
      rw [e2, hreal]
      show _ = (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
      rw [mul_assoc]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_apply, hkey]
    rfl
  obtain ⟨a₀, ha₀, k, hk, rfl⟩ := (GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D (Formalism.IndefR.Links.Vc D j)).1 g
  obtain ⟨w, rfl⟩ := (hAg.PV j).onto k hk
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec hμ j f'
  have hw := hfin w
  rw [← hy] at hw ⊢
  have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
      X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ) =
        (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := fun γ hγ =>
    (congrArg (X.R.extV j (X.tupT (D.nd.mu i)) y) (mul_assoc _ _ _)).trans
      (extV_inf X j _ y ha₀ (mul_mem ((hAg.PV j).into w) (rep_mem _ Pp d hγ)))
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := Finset.sum_congr rfl e1
    _ = (X.R.cV j).ρ a₀⁻¹ (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := (map_sum _ _ _).symm
    _ = (X.R.cV j).ρ a₀⁻¹ (c • X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := congrArg _ hw
    _ = c • (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := map_smul _ _ _
    _ = c • X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w) :=
      congrArg _ (extV_inf X j _ y ha₀ ((hAg.PV j).into w)).symm
end GlobalTheory.SummandEig
end
