import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem isIdemAt_idemAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    Formalism.L2.NTheta.IsIdemAt (idemAt w) w := by
  have h : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w := by
    rcases Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩
    · exact b ▸ G.pl.w_split _ a
    · first
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b h
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h)
  exact Classical.epsilon_spec h

theorem chi_charUnramAt (G : GridData L sc) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∉ G.pl.S0) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.ch.chi k) v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq k h1 h2) w).2 (G.ch.unr k h1 h2 w (by rwa [hw]))

theorem eta_charUnramAt {μ₀ : T} (hL : L.Is μ₀) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D L.eta v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)

theorem attChr_charUnramAt {χ η : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hχ : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v) (hη : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D η v) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.attChr χ η n) v := by
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul hχ (GlobalTheory.SeeSaw.WeilLines.charUnram_inv hη)
  · exact hχ

theorem notMem_S0_of_no_place_above (G : GridData L sc) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) : v ∉ G.pl.S0 := by
  classical
  intro h
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl
    exact Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ h)
  exact hv _ hw (G.pl.under_w h)

end GlobalTheory.RowVacScalar

theorem GlobalTheory.RowVacScalar.vacScalar_eq_prod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
    ∀ q : GA D (G.pS (.chi i D.R.m)) × GA D (G.pT (.chi i D.R.m)), q.1 ∈ GfC (G.pS (.chi i D.R.m)) → q.2 ∈ GfC (G.pT (.chi i D.R.m)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E))) →
    ∀ c : ℂ, W.om (.chi i D.R.m) q (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) →
    c = ∏ w : locPl G t, GlobalTheory.RowVacScalar.splitScal G (.chi i D.R.m) w.1 q.1 q.2 := by
  intro D T L sc G W U S μ₀ hL t i hi q hq1 hq2 hS hT c hc
  classical
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have hW := W.om_is (.chi i D.R.m) hp
  have sd := GlobalTheory.RowVertexInv.FactorTheta.selfDual S hi
  have hv := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2
  have key := GlobalTheory.T.weilLatticeVacuum_eq_prod_splitPlace_factors hW sd.1 sd.2 (locPl G t) (fun w hw => isIdemAt_idemAt hL G t hw)
    (Good.under_injOn hL G t) (fun v hv' => by
      have hχ := chi_charUnramAt G (k := D.R.m - i) (by omega) (by omega) (notMem_S0_of_no_place_above G t hv')
      exact ⟨attChr_charUnramAt hχ (eta_charUnramAt hL v) _, attChr_charUnramAt hχ (eta_charUnramAt hL v) _⟩)
    q.1 hq1 q.2 hq2 hS hT _ hv.theta hv.lat
  have hne := GlobalTheory.RowVertexInv.FactorTheta.vac_ne_zero S hi
  have e1 : c • S.Z.vac (.chi i D.R.m) = (∏ w ∈ locPl G t, splitScal G (.chi i D.R.m) w q.1 q.2) • S.Z.vac (.chi i D.R.m) :=
    hc.symm.trans key
  rw [Finset.prod_coe_sort (locPl G t) (fun w => splitScal G (.chi i D.R.m) w q.1 q.2)]
  exact smul_left_injective ℂ hne e1
