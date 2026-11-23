import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentOfRecordVsFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExponentLogLeOfCut
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Asm

open Formalism.L2.Indef Formalism.L2.Indef.Tree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jexpU_le_jrec7 (hcut : Formalism.CohomologicalDescent.E.ExCut) {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G]
    [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι) (hN : NumOk P W)
    (hoff : ¬ W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → LIncl B ℓ Z w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)))
    (hin : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∃ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam),
      Covers B ℓ Z w X ∧ ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) :
    B.JexpU ℓ Z w ≤ (W.Jrec7 P (Formalism.EigenvalueLevelCeiling.plc w) : ℚ) := by
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime w
  have hrec := GlobalTheory.exponent_of_record_vs_formulas hcut P hN.1 hN.2.1 ι W hN.2.2.1 _ hp
  by_cases hR : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w)
  · obtain ⟨fr, cj, I, X, hc, hX⟩ := hin hR
    have h1 := GlobalTheory.T.primePowerLatticeInclusion_of_localModels K G Pl0 B ℓ Z w ι P W hN hp hR fr cj I X hc hX
    have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ h1).2
    rw [hrec.2 hR] at h2
    exact h2
  · have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ (hoff hR)).2
    exact h2.trans (by exact_mod_cast hrec.1 hR)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem splitPartNumbers_exponent_eq_liftExponent (C CH : ℝ) (t : p.P.T) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    ((R2 p).num (F2 p) C CH).J0 t w j = (((blk p j t).JexpU (lvlL p) (subZ p j t) w : ℚ) : ℝ) := rfl

open Classical in

theorem hasExpBound_at (hcut : Formalism.CohomologicalDescent.E.ExCut) {c : OnConst} (O : Obj p c)
    (hm : O.m = (D.R.m : ℝ)) (hx : O.x = L.sc.x) (heps : O.eps = L.sc.eps) (hT2 : O.T2 = D.host.T2.card)
    (Pj : Fin D.R.m → Par) (Wj : Fin D.R.m → Wts D.what₂.Tau) (hD : ∀ j, Dict L j (Pj j) (Wj j))
    (hN : ∀ j, NumOk (Pj j) (Wj j))
    (hS : ∀ j t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w ((Wj j).JA (Pj j) (Formalism.EigenvalueLevelCeiling.plc w)))
    (hM : ∀ j, ∀ w ∈ p.R.twPl, (Wj j).WRange (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j (Pj j) (Wj j) w) (C CH : ℝ) :
    HasExpBound ((R2 p).num (F2 p) C CH) O := by
  refine ⟨fun w _ j => ?_, fun j l => ((Wj j).Jrec7 (Pj j) l : ℝ), fun j => ⟨fun l => Nat.cast_nonneg _, fun Q hQ => ?_⟩,
    fun w hw j => ?_⟩
  · have h := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion _ _ _ _ _ _ w _ (hS j ((S2 p).μ w) w)).1
    rw [splitPartNumbers_exponent_eq_liftExponent]
    exact_mod_cast h
  · obtain ⟨hHyp, hLarge, hOk, X', A, hRows, hBig⟩ := hN j
    have hcard : Fintype.card D.what₂.Tau = (Pj j).f := by rw [← Nat.card_eq_fintype_card]; exact (hD j).card
    have h := UpperTheory.ExcSet.sum_exponent_log_le hcut D (Pj j) X' A hHyp hLarge hRows hBig D.what₂.Tau (Wj j) hOk hcard (hD j).f
      (hD j).special O.T2
      (by rw [hT2]; exact (hD j).thick) Q hQ
    have hxe : O.xe = (Pj j).L := by rw [(hD j).log]; show O.x ^ O.eps = _; rw [hx, heps]
    have hb : O.b = (Pj j).b := by rw [(hD j).b]; show Real.exp O.xe = _; rw [hxe, (hD j).log]; rfl
    have hm' : O.m = ((Pj j).m : ℝ) := by rw [hm, (hD j).m]
    show _ ≤ 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
    rw [hxe, hb, hm']
    exact h
  · have hle := jexpU_le_jrec7 hcut (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w (Pj j) (Wj j) (hN j)
      (fun _ => hS j _ w) (fun hR => hM j w hw hR)
    show (((blk p j (p.R.mu w)).JexpU (lvlL p) (subZ p j (p.R.mu w)) w : ℚ) : ℝ) ≤ ((Wj j).Jrec7 (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) : ℝ)
    exact_mod_cast hle

end Point

theorem expSt_of : Formalism.CohomologicalDescent.E.ExCut → NumSt → SumExpSt → ModelSt → ExpSt := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'

end GlobalTheory.ExpTie.Asm

end
