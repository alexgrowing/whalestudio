import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LatOfHasLoc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in

theorem mem_latGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m)
    (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j h1 hj x g hx hg
  obtain ⟨e, he, hsupp, hloc⟩ := hx
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e0 : infPart D e = 0 := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1
  have e0' : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  refine ⟨GlobalTheory.LevelCut.mem_GfC_of _ x fun i k => ?_, ?_⟩
  · rw [← hsupp i k, map_mul, map_add, e0, e0', add_zero, zero_mul]
  · have hl : ∀ (w : Pl D.host.E) (X : ℕ × ℕ), 1 ≤ X.1 → 1 ≤ X.2 →
        givenLevel ch.G t w X = GlobalTheory.SplitWeil.KO (Kw w) _ := by
      rintro w ⟨_ | a, _ | b⟩ h h'
      · omega
      · simp at h
      · simp at h'
      · rfl
    have hβ : IsFrame (ch.S.B.β D.R.m j) (ch.G.Λ (.grid D.R.m j)) := ch.S.B.isFrame_β hS.core.lev le_rfl hj
    have hsd : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
      (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun k h => by
        have := (Node.grid.inj h).1; omega).sd
    set c : Lev.EAf D := toEAf D (e + cA D e) with hc
    have hX : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val =
        c • (Lev.finE (ch.G.V (.grid D.R.m j)) x).val + (1 - c) • (1 : Matrix _ _ (Lev.EAf D)) := by
      have hM : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val = (mt _ x).map (toEAf D) := rfl
      rw [hM]
      ext i k
      have h0 := congrArg (toEAf D) (hsupp i k)
      rw [map_mul, Matrix.sub_apply, map_sub] at h0
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
      by_cases hik : i = k
      · subst hik
        simp only [Matrix.one_apply_eq, map_one] at h0 ⊢
        rw [← hc] at h0
        linear_combination -h0
      · simp only [Matrix.one_apply_ne hik, map_zero, sub_zero, mul_zero, add_zero] at h0 ⊢
        exact h0.symm
    have key := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA (V := ch.G.V (.grid D.R.m j)) (Λ := ch.G.Λ (.grid D.R.m j))
      (β := ch.S.B.β D.R.m j) hβ hsd (locPl ch.G t) (n' := fun w => (locGrid ch.G t w.1).rank (D.R.m, j))
      (fun w => rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) fun _ => rfl
    have hmax : Lev.finE (ch.G.V (.grid D.R.m j)) x ∈ ch.G.levMax (.grid D.R.m j) := by
      rw [GridData.levMax, ← key]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
        Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_⟩, GlobalTheory.LevSplit.finE_mem_UA _ x⟩
      · rw [Subgroup.mem_comap, hloc w]
        have := hg w
        rw [hl w.1 (D.R.m, j) hm h1] at this
        exact this
      · rw [Subgroup.mem_comap, (GlobalTheory.OffPartLattice.inBasis_mix (ch.S.B.β D.R.m j) _ _ c hX w').1
          (GlobalTheory.OffPartLattice.cpt_pair_zero (ch.G.V (.grid D.R.m j)) he w' hw')]
        exact one_mem _
    exact hmax

end GlobalTheory.LatOfHasLoc
