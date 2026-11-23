import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowSingle

theorem locPl_under {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  intro w hw
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with h | h
  · left
    unfold Places.W0 at h
    obtain ⟨v, hv, rfl⟩ := by simpa only [Finset.mem_image] using h
    rw [G.pl.under_w hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

theorem exists_rowData {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    {μ₀ : T} (hL : L.Is μ₀) (ρ : RealMatch W) (t : T) (e : AE D) (he : IsIdemSum e (locPl G t))
    (F : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (fr : SchRow G)
    (hfr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (F i) (fr i)) :
    ∃ (dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m))
      (cr : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) →₀ ℂ),
      (∀ i, (dr i).e = e ∧ IsCombOf W (dr i) (cr i)) ∧ (∀ i, comb W.ψ _ _ (cr i) (ρ.vX i D.R.m) = fr i) ∧
        ∀ i, (dr i).fn = F i := by
  let dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m) := fun i =>
    { FinDatum.ind G t (.chi i D.R.m) (locPl G t) (locPl_under G t) e he with fn := F i, sb := (hfr i).1 }
  let d : PureDat G t := (fun j => FinDatum.vacuum G t (.top t j), dr)
  obtain ⟨c, hc⟩ := GlobalTheory.CombsExist.exists_isCombs W hL (Finsupp.single d 1)
  have hc' := (hc d (by simp)).2
  refine ⟨dr, fun i => (c d).2 i, fun i => ⟨rfl, hc' i⟩, fun i => ?_, fun i => rfl⟩
  have hv := ρ.vX_is i D.R.m i.2 le_rfl
  obtain ⟨⟨Tm, hTm⟩, h1⟩ := (hc' i).2.2 (ρ.vX i D.R.m) hv.2.theta hv.2.lat
  exact (h1 Tm hTm).trans ((hfr i).2.2 Tm hTm).symm

theorem rowData : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t e he φ fr hfr
  obtain ⟨dr, cr, h1, h2, h3⟩ := exists_rowData ch.W s.core.lev ch.rm t e he _ fr hfr
  exact ⟨dr, cr, h1, h2, fun i y hy => by rw [h3 i]; exact if_pos hy⟩

end GlobalTheory.RowSingle
