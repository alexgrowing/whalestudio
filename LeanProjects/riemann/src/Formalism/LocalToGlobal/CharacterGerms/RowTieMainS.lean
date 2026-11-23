import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTieMain
import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
import Formalism.SharpRestriction.GrowthBounds.ProofRowTieVals
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfU
import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjHolds

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def UnitSelfAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)), UnitSelfSt Y p

def GermLiftSelfAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V), GermLiftSelfSt Y p H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoInS : Prop where
  lab : LabSGeoCoreSt Xo c
  ndg : NondegenerateCharts Xo c

  ch : CharacterHypothesisSelfUnramified Xo c

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem hypsSelf_main (G : GeoInS Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E)))) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha (labSGeo_of_core Xo c G.lab hstar T io y C3 C V ι hι k Y hY Orb 2 lab ha) o)).Hyps V :=
  hypotheses_of_self_labelling_unramified (cartesian_self_conj_of_stability ptSelf_holds hStabSelf_holds) axesSelf_holds SelfConjugateGermZero.germ_zero_self_conjugate cEqSelf_holds independence_bound_self_conjugate
    (rank_maximal_self_charts_of_nondegenerate Xo c rank_maximal_self_unconditional G.ndg) G.ch hstar hι hd hY ha _ hr o

theorem rowTieSelf_main (G : GeoInS Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E)))) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hr : lab.RankOK Dw) :
    ∃ X : ∀ o, RowData C V 2 (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o),
      (∀ o, (X o).n = lab.n ∧ (X o).m = lab.j + lab.j' ∧ (X o).rh = 0 ∧ (∀ g b, (X o).big g b ↔ lab.big o g b) ∧
        ∀ (g : Fin 2) (x : lab.II Dw o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + lab.hd) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n →
        ∀ (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n) (F : ∀ o, Flag (X o)) (nW : ℕ), nW ≤ 2 * N + 1 →
        ∀ gaC : Orb → ZMod 2 → ℕ → ℕ,
        (∀ o g t (q : Fin ((X o).rkF g t)), ((F o).en g t q).2.val = q.val) →
        (∀ o, (X o).Alt) → lab.j' < lab.n → (∀ o s q, gaC o s q ≠ 0 → 1 ≤ q ∧ q ≤ (X o).rkF 0 s) →
        WtTieC Dw.mult lab.tau gaC (fun τ i => a (τ, i)) →
        ValBlocksC X F nW gaC ν := by
  refine ⟨fun o => rdS Y (selfOfLab ha (labSGeo_of_core Xo c G.lab hstar T io y C3 C V ι hι k Y hY Orb 2 lab ha))
    (hypsSelf_main G hstar hι hd hY ha hr) o, fun o => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩, ?_⟩
  intro a n ν hν N pl F nW hn gaC std hA hj supp tie
  exact value_blocks_self_conj_finite (descent_holds Xo c) hι hY ha _ (hypsSelf_main G hstar hι hd hY ha hr) a n
    (valuation_eq_self_of_unit_germ Y _ _ _ n (unitSelf_holds Y _) (germLiftSelf_holds Y _ _)) ν hν pl F nW hn gaC std hA hj
    supp tie

end Formalism.L2.FormalSeriesBounds
