import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndex
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastRowCongOfKeepsPairsStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem GlobalTheory.FamTrace.uloc_T_of_inLevG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hF := hA.tr.std.some u
  have hI := hA.tr.ok
  have hP := hA.tr.pins.some
  obtain ⟨kk, R⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have hlb := R.lb ()
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s (W.R.T.cols.forms u).atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact (W.R.T.cols.forms u).atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N 0) ((((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ (W.R.T.cols.forms u).atT.piU hp0 _ ?_
    rw [hF.piU]; exact hlb
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) := by
    have h1 := hPr.piT_cop u
    have e : s (W.R.T.cols.forms u).atT.piU = B.fields.conjO ((B.primes X).piT u) := by
      apply RingOfIntegers.ext (K := (I.rec7 l Z).host.E)
      rw [hsc, hF.piU]
      exact (B.fields_conjO_coe _).symm
    rw [e, hF.piU]
    exact h1
  have hint : ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r t : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) w (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r t) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E w :=
    GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice (I.rec7 l Z) ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (a.g.x 0).L
      ((hat.std.2 0 (Nat.zero_le _)).1) κ hIn.1
  refine GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime (Formalism.L2.Forms.sigD (I.rec7 l Z)) (fun x => star_star x) hgram (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) rfl hpq hcop hTp.ne_zero hL v hv _ (GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2) ?_ ?_
  · intro r t
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 r t) ∈ _
    rw [← hy]
    exact hint v r t
  · intro t
    obtain ⟨c, hc, he⟩ := _root_.GlobalTheory.T.true_geometry_final_character_alt W hA u a ha hat κ hκ hIn.2.1 hint v hv t
    refine ⟨c, hc, ?_⟩
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 _ t) - _ = _
    rw [← hy, he, hF.piU]
    rfl
end
end
