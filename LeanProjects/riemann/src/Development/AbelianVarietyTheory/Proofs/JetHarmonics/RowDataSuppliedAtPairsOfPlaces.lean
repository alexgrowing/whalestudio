import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GeZeroOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GermsDerivKernelOfFormal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstOneVariableUncurryEqSubst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChartStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlacesStatement

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_pairs : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb _ d _ lab ha hsurj hr hj hdich a hdom nW ν hν
  have hg : LabGeo C3 ι Y lab :=
    GlobalTheory.LabelledDirections.labGeoSt E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hnd : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V := fun o =>
    FBChart.hyps GlobalTheory.cartHyp_of_formalBiextension axesFB GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.2 Y (pairOfLab ha hg o)
      (rankHyp_ofLab ha hg hr o)
      (GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal.2 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) hnd (rankHyp_ofLab ha hg hr o) _)
      (GlobalTheory.T.characterBound_pairs_of_places_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl Orb d lab ha hg hr o _)
  have hfl := fun o => GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
    (fun _ => Equiv.refl _) (JJ (lab.II Dw o)) (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)
  have hrk : ∀ o g s, (RF.rd Y (pairOfLab ha hg) Hy o).rkF g s = Dw.mult (lab.tau o g s) := fun o => (hfl o).1
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o => lab.II Dw o, fun o => JJ (lab.II Dw o), inferInstance, inferInstance,
    fun o => RF.rd Y (pairOfLab ha hg) Hy o, F, fun o => ⟨rfl, rfl⟩, fun o _ g s => ⟨Iff.rfl, hrk o g s⟩, ?_⟩
  refine RF.valBlocks_of_nuPlE Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW F Finset.univ _ ν
    (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW))
    (pairsSep_ofLab ha hg) (GlobalTheory.RowVal.value_eq_prod C V (𝓞 E) _ Y d Orb _ (pairOfLab ha hg) Hy _ nW) GlobalTheory.JetProd.jetProd
    (GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hsurj hr hj Hy F
      (fun o g s q => (hF o g s q).2) a hdom nW) ?_
  refine RF.blkAdm _ F Finset.univ _ (fun o _ => hdich o) (fun _ _ => hj) fun o _ g s q hq => ?_
  rw [hrk]
  by_contra hc
  exact hq (by unfold gap; rw [if_neg fun h => hc h.2])

end GlobalTheory.RowAt
