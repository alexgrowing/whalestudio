import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundSelfConjugateDegreeTwoIntegralCharStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowDataStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemAtSelfConjPlacesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowConditionTwoSelfConjugateOfNonDegenerateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSelfConjugatePlaceDataIntChartStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanesStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def pairCols (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

def tyShift (g : Fin 2) : ZMod 2 ≃ ZMod 2 := if g = 0 then Equiv.refl _ else Equiv.addRight 1

theorem supplyC_selfConj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → SupplyC V Orb lab.n (lab.j + lab.j') (fun o s => Dw.mult (lab.tau o s)) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ lab ha hsurj hr hj a hdom nW ν hν
  obtain ⟨p, hp, hsep, hrk⟩ := GlobalTheory.T.exists_selfConjugatePlaceData_intChart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha
  obtain ⟨hCart, hAx, hG0, hC, hR1⟩ := GlobalTheory.T.rowLaw_formal_statements_selfConjugate
  have hndg : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.rawSelf (p o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y 2 _ (p o)
      rank := (hrk hr o).1
      axes := hAx C V (𝓞 E) _ Y 2 _ (p o)
      G0 := hG0 C V (𝓞 E) _ Y 2 _ (p o) _
      CEq := hC C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
      R1 := hR1 C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
        (GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _)
      R2 := GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _
      CH := GlobalTheory.T.characterBound_selfConjugate_degreeTwo_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb lab ha hr p hp o _ }
  have hfl := fun o => GlobalTheory.T.flag_of_letterNumbering_rowData C V 2 (fun _ => ZMod 2) (fun _ s => Dw.mult (lab.tau o s)) tyShift
    (JJ fun _ => lab.II Dw o) ((Y.rawSelf (p o)).rowData (Hy o)) (by
      intro g x
      show (if g = 0 then (p o).ty0 x else (p o).ty0 x + (p o).hd) = _
      rw [hp.ty0, hp.hd]
      unfold tyShift
      split_ifs <;> rfl)
  have hrkF : ∀ o s, ((Y.rawSelf (p o)).rowData (Hy o)).rkF 0 s = Dw.mult (lab.tau o s) :=
    fun o s => (hfl o).1 0 s
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o _ => lab.II Dw o, fun o => JJ fun _ => lab.II Dw o, inferInstance, inferInstance,
    fun o => (Y.rawSelf (p o)).rowData (Hy o), F, fun o => ⟨hp.n o, ?_, (hrk hr o).2, hrkF o⟩, ?_⟩
  · show (p o).j + (p o).j' = _
    rw [hp.j, hp.j']
  · refine RF.valBlocksC_G (n := nW / 2)
      (GlobalTheory.T.chartValues_bound_products_on_planes C V (𝓞 E) _ Y 2 Orb _ p Hy (chartLetterSystem C3 V ι a) (nW / 2) nW (pairCols nW) ν hsep
        (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW)))
      GlobalTheory.JetProd.jetProd F nW (by omega) _
      (GlobalTheory.T.blockProd_mem_at_selfConj_places E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha hsurj hr hj p hp Hy F
        (fun o g s q => (hF o g s q).2) a hdom (nW / 2) nW (pairCols nW)) ?_
    refine RF.blkAdmC _ F _ (fun o => (hrk hr o).2) (fun o => ?_) (fun o s k' hk => ?_)
    · show (p o).j' < (p o).n
      rw [hp.j', hp.n]
      exact hj
    · rw [hrkF]
      by_contra hlt
      apply hk
      unfold gap
      rw [if_neg (fun h => hlt h.2)]

end GlobalTheory.RowAt
