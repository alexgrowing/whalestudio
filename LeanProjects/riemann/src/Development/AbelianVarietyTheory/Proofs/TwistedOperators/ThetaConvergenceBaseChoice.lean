import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMatchingOfBaseChoiceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

theorem row_lifts_base : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  intro hP hL D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs a u
  obtain ⟨G', hG', hM⟩ := GlobalTheory.T.grid_matching_of_base_choice hP large₂ hS ch hb CF hs
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.CuspAlong G' :=
    hL D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hS.size) Γ Pl0 T A Ks R G' (rowBase_of_core hS.core) hG'
  let C : ∀ i, Set (Fn ch.G (.grid i 0)) := fun i =>
    {φ | ∃ Φ' ∈ (G'.V i 0).Cusp R.θ, ∃ v, HEq (Φ' v) φ}
  have step : ∀ (i : Fin D.R.m) φ, φ ∈ C i → LiftConv ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∧
      liftA ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∈ C ((i : ℕ) + 1) := by
    rintro i φ ⟨Φ', hΦ', v, hv⟩
    obtain ⟨f, hf, p, hK⟩ := hM.ker ch.ρ (ch.Phi a) i
    obtain ⟨F', hF', H⟩ := hC.X A.μ0 i 0 i.2 (Nat.zero_le _) f hf Φ' hΦ'
    rw [G'.meas_zero] at H
    have T := transport_stepS (hM.V i i.2.le) (hM.V (i + 1) i.2) (hM.ν i i.2.le) (hM.fd i i.2.le) hK hv
      (fun h => (H p v h).1) (fun h => (H p v h).2)
    exact ⟨T.1, F', hF', _, T.2⟩
  have h0 : ch.form u ∈ C 0 := ⟨_, start_mem hS.core u, ch.w, HEq.rfl⟩
  obtain ⟨h1, Φ', hΦ', v, hv⟩ := row_induction ch.W ch.M C D.R.m _ step _ h0
  exact ⟨h1, isAutFun_transportS (hM.V _ le_rfl) hv (isAutFun_of_mem_cusp _ R.θ hΦ' v)⟩

end GlobalTheory.RowLift

end
