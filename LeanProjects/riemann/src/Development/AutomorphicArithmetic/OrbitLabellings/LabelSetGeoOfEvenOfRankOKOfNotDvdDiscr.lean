import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
import Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfLabelSetArith
import Development.AutomorphicArithmetic.OrbitLabellings.LabelSetEvOfGeoOfNotDvdDiscr
import Development.AutomorphicArithmetic.OrbitLabellings.BlkMemSSelfConjugatePlacesOfCMDatum
import Development.AutomorphicArithmetic.OrbitLabellings.ValBlocksSOfBlkMemS

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private def pairColsS (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

theorem UpperTheory.labelSetGeo_of_even_of_rankOK_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) → lab.j' < lab.n →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (ga : Orb → ZMod d → ℕ → ℕ),
    (∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ Dw.mult (lab.tau o s)) → WtTieS Dw.mult lab.tau ga (fun τ i => a (τ, i)) →
    ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW →
    ∃ (X : ∀ o, RowData C V d (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o)) (F : ∀ o, RF.Flag (X o)),
      (∀ o, (X o).n = lab.n ∧ (X o).m = lab.j + lab.j' ∧ (X o).Alt ∧ ∀ s, (X o).rkF 0 s = Dw.mult (lab.tau o s)) ∧
      ValBlocksS lab.hd X F nW ga ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ d _ lab ha hdisc hev hr hbig hj
    a ga hsupp htie nW ν hν
  have hg : LabSGeo C3 ι Y lab := UpperTheory.labelSetGeo_of_labelSetArith E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hR2 : RankMaximalSelfCharts Xo c := rank_maximal_self_charts_of_nondegenerate Xo c rank_maximal_self_unconditional (GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c)
  have hCart : CartSelfSt := cartesian_self_conj_of_stability ptSelf_holds hStabSelf_holds
  have Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      rank := rankHyp_ofLabS ha hg hr o
      axes := axesSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      G0 := SelfConjugateGermZero.germ_zero_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) _
      CEq := cEqSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
      R1 := independence_bound_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
        (hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
      R2 := hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _
      CH := UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb d lab ha hg hdisc hev hr hbig o _ }
  have hty : ∀ o (g : Fin 2) (x : lab.II Dw o),
      ((rdS Y (selfOfLab ha hg) Hy o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + lab.hd := fun _ _ _ => rfl
  have hrk : ∀ o g t, (rdS Y (selfOfLab ha hg) Hy o).rkF g t = Dw.mult (lab.tau o (idxS lab.hd g t)) :=
    fun o g t => rkF_sigmaS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o) g t
  have hrk0 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s = Dw.mult (lab.tau o s) := fun o s => hrk o 0 s
  have hrk1 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 1 (s + lab.hd) = (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s
    rw [hrk0, hrk]
    have e : idxS lab.hd 1 (s + lab.hd) = s := by
      unfold idxS
      rw [if_neg (by decide), add_sub_cancel_right]
    rw [e]
  have hA : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt := fun o => ⟨hev, hbig o⟩
  have hsupp' : ∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s k' h
    rw [hrk0]
    exact hsupp o s k' h
  refine ⟨fun o => rdS Y (selfOfLab ha hg) Hy o,
    fun o => stdFlagS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o),
    fun o => ⟨rfl, rfl, hA o, hrk0 o⟩, ?_⟩
  exact UpperTheory.valBlocksS_of_blkMemS C V d lab.hd ha.hd_two Orb _ _ _ (nW / 2) _ ν
    (RF.valO_self Y (selfOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW ν
      (hν.trans (descent_holds Xo c T io y C3 C V ι hι k Y hY a nW)) (selfSep_ofLab ha hg)
      (valuation_eq_self_of_unit_germ Y _ _ _ nW (unitSelf_holds Y _) (germLiftSelf_holds Y _ _)) (pairColsS nW))
    _ nW (by omega) ga
    (UpperTheory.blkMemS_selfConjugate_places_of_CMDatum E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg Hy a (nW / 2) nW (pairColsS nW) _ ga
      (fun _ _ _ _ => rfl) hA hj hsupp' htie)
    hA (fun _ => hj) hrk1 (fun o s k' h => (hsupp' o s k' h).2)
