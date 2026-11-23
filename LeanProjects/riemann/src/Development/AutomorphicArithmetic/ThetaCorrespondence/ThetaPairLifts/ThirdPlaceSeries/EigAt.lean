import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.PtLocalPin
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
theorem eig_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (w : PlE D.host) (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hcw : IsConjPl D.host w s.w)
    (hu : IsUnif D.host.E s.v ϖ) :
    ∃ c : ℕ → ℂ, X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.naut.locV i Q w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ k, 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i Q,
        NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) = c k • (P.M.loc i).real y := by
  classical
  have HT := P.H.hecke
  have hsB : s.v ∉ badPl D i := GlobalTheory.HeckeScalarAll.not_bad HT i hw s hcw
  have hex : ∀ k, ∃ c : ℂ, ∀ f ∈ P.H.av.S i Q,
      (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) →
      NG.tN (Umax D.host.E D.R.nV) s ϖ k f = c • f := fun k =>
    GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s ϖ k hu
  choose c hc using hex
  have hfT : ∀ y, (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    intro y
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : ∀ y ∈ D.naut.typeV i Q, (P.M.loc i).real y ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro y hy
    rw [P.H.av.typeV] at hy; exact hy
  have hfix : ∀ y, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real y) = (P.M.loc i).real y := by
    intro y κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ :=
      GlobalTheory.HeckeScalarAll.trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := (hfT y).2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    have hf0 : (P.M.loc i).real y0 ≠ 0 := fun h =>
      hy00 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
    obtain ⟨g, hg, hg0, hgfix⟩ := exists_fixed_of_isoTyp (P.H.av.irr i Q) s.v _ (hfI y0 hy0) hf0 (hfix y0)
    have hpol := P.H.au.locPol (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) s w ϖ hcw hu
      (Umax D.host.E D.R.nV) (fun κ _ => Iff.rfl) g hg hg0 hgfix c (fun k _ _ => hc k g hg hgfix)
    rw [hpol, D.nbc.embAV_loc, P.H.emb]
  · intro k _ _ y hy
    have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
      (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
    have e1 : NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) =
        NG.tN (Umax D.host.E D.R.nV) s ϖ k ((P.M.loc i).real y) := by
      simp only [NG.tN]
      rw [GlobalTheory.HeckeScalarAll.heckeD_eq_of_fixed (P.M.loc i).J (P.M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _
        (hfix y)]
    rw [e1]
    exact GlobalTheory.HeckeScalarAll.tN_isoTyp (P.H.av.irr i Q) s ϖ k hfinU (c k) (hc k) _ (hfI y hy) (hfix y)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i,
    GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro hL D P i
  refine GlobalTheory.T.pointLocalEigen_galoisPolynomial_split D P.M P.H.hecke P.H.rational P.H.av P.H.cover i ?_
  intro Q w hw
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  obtain ⟨c0, hp0, -⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s0 ϖ0 hc0 hu0
  have hN : normV w ≠ 0 := (lt_trans zero_lt_one (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  refine ⟨c0, hp0.symm, fun k s ϖ hc hu h1 h2 y hy => ?_⟩
  obtain ⟨c, hp, hy'⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s ϖ hc hu
  rw [hy' k h1 h2 y hy, coeff_eq hN (hp.trans hp0.symm) h1 h2]
end GlobalTheory.PtLocalPin
end
end
