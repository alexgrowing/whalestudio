import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.LastRow
end GlobalTheory.FamTrace.LastRow
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ → (∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r s : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r s) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ s : Fin ((I.rec7 l Z).R.N 0), ∃ c ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v, Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ (Formalism.L2.Col.lastIdx _) s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N 0)) (Fin ((I.rec7 l Z).R.N 0)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (Formalism.L2.Col.lastIdx _) s = Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)) * c := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat κ hκ hkp hint v hv s
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have htP : ∀ p, p ∈ a.v.tP ↔ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal := by
    have hψ := hat.pinX.std
    let row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t := fun t =>
      { vP := fun _ => 0, vT := fun _ _ => 0,
        sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
        sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some,
        io := fun _ => 0, ioT := fun _ _ => 0 }
    exact (ha.tie row (fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, fin := fun _ => inferInstance, dd := fun _ _ _ => 0, e := fun _ _ => 0,
        eT := fun _ _ _ => 0, Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1,
        cK := fun _ => 1, cP := 1 })).1.tP
  obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 ((htP v).2 hv)
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  obtain ⟨e, he⟩ := hat.std.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hn := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  set r₀ : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm (Formalism.L2.Col.lastIdx _) with hr₀def
  set s' : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm s with hs'def
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X 0).rank := by
    have h1 : (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 = (I.rec7 l Z).R.N 0 - 1 := rfl
    have h2 : r₀.1 = (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 := rfl
    have h3 := NeZero.ne ((I.rec7 l Z).R.N 0)
    omega
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u a.k a.ι a.o.p a.o.β a.o.Q _ hat.std 0 (Nat.zero_le _) i r₀ hr₀
  obtain ⟨g, hg⟩ := GlobalTheory.FamTrace.LastRow.exists_gl (a.o.β 0 i) κ
  have hl := GlobalTheory.FamTrace.LastRow.row_lt_of_smul_pair_eq _ _ _ _ (a.o.β 0 i).bb' _ r₀ hQ g hg (hkp i g hg) s'
  exact GlobalTheory.FamTrace.LastRow.entry_cong (I.rec7 l Z) a.k (a.o.p i) (e i).1 (he i) ((I.rec7 l Z).mem u).A.T (X.piT u)
    (B.fields.conjO (X.piT u)) ((B.fields_conjO_coe _).trans (GlobalTheory.RankOneLine.star_eq_hostConj (I.rec7 l Z) _).symm)
    (hPr.piT_norm u) (hPr.piT_cop u) hpi hv (GlobalTheory.LevelUnif.T_notMem_sq (I.rec7 l Z) u (W.R.T.cols.forms u).atT _ hv)
    _ hn κ _ s (hint _ _ s) hl
end
end
