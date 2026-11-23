import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EntryAOneParity
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AtPiEqRescale

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime]

def ea_RestSExpV (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be → ∀ (j : ℕ) (v : X.Pl),
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-(
            ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
              sub2 p be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩)) :
            MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p))))))) =
          expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V

theorem ea_restSU_of (X : Sys p) (Y : Pend X) (hE : ea_RestSExpV X) : ea_RestSU X Y := by
  intro hD hbe v j U hU K' _ _ _ _ R' vp hvp hRp hOc
  obtain ⟨u, hu, V, hV, heq⟩ := hE hD Y.be hbe j v Y.Kc K' vp hvp
  have heq' : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
      (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))))) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V := heq
  refine ⟨u, fun s => hRp (hu s), ?_⟩
  rw [ThZA_mul, map_mul, atPi_mul, heq', mul_assoc]
  have hW : IntR R' (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) :=
    restSIntA (X := X) j Y.Kc Y.Oc U hU K' R' vp hvp hRp hOc
  have hVW := IntR_mul (fun n => hRp (hV n)) hW
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K') p]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  exact inClass_of_exp hp0 (fun k => hRp (piFact (p := p) (vp := vp) (hvp := hvp) (k := k))) (X.hhA K' j v u) (hhA_const (X := X) K' j v u) hVW

theorem ea_three (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hE : ea_RestSExpV X) (h1 : SeriesGaussValuationFirst X)
    (h2 : SeriesGaussValuationSecond X) (h3 : ea_RestKerB X) : EntryBoundOfHypotheses X Y D ∧ PlacewiseLowerBoundEvenShift X Y D ∧ RestBU X Y D :=
  ⟨first_theorem_place_of_series D Y (ea_restSU_of X Y hE) h1, second_lemma_place_of_series D Y (ea_restSU_of X Y hE) h2,
    ea_restBU D Y (ea_restSU_of X Y hE) h3⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
