import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLastColumnLevelIffGridVertexLevelVolumeOnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTopLevelLastIffGridVertexLevelVolumeOneStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.TermScales

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem finE_toFin' (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  have hx : Lev.finE V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 from (GlobalTheory.AutMult.toInf V g).2, map_one]
  rw [map_mul, hx, one_mul]

theorem isAt_congr (M : Vol G) (X : Node) {K K' : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (hK : ∀ k : FinPt G X, finG (G.V X) k ∈ K ↔ finG (G.V X) k ∈ K') (h : M.IsAt X K) : M.IsAt X K' := by
  have hK' : ∀ g : GA D (G.V X), Lev.finE (G.V X) g ∈ K ↔ Lev.finE (G.V X) g ∈ K' := by
    intro g
    rw [← finE_toFin' (G.V X) g]
    exact hK (GlobalTheory.AutMult.toFin (G.V X) g)
  unfold Vol.IsAt at h ⊢
  split_ifs at h ⊢
  · simpa only [IsMeasDef, Lev.IsMeasLevDef, Lev.IsMeasLevW, hK'] using h
  · simpa only [Lev.IsMeasFD, Lev.IsMeasLev, Lev.IsMeasLevW, hK'] using h

theorem isHaar_of_isAt (M : Vol G) (X : Node) {K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))} (h : M.IsAt X K) :
    (M.ν X).IsHaarMeasure := by
  unfold Vol.IsAt at h
  split_ifs at h
  · exact h.1.1
  · exact h.1.1

end GlobalTheory.TermScales

open GlobalTheory.TermScales in

theorem GlobalTheory.TermScales.exists_scales : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (M M' : Vol ch.G), M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
    ∃ x : Node → ℝ≥0, Scales M M' x ∧
      ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → x X = 1 := by
  refine big_mono ?_ (Big.and GlobalTheory.T.rowTest_lastColumn_level_iff_gridVertexLevelVolumeOne GlobalTheory.T.rowTest_topLevel_last_iff_gridVertexLevelVolumeOne)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hch
  obtain ⟨hrow, htop⟩ := hch
  intro t Φ β M M' hM hM'
  have hdef : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → Node.InRange D.R.m X := by
    intro X hX _
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  have hM'at : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → ∃ K, M'.IsAt X K := by
    intro X hX hne
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨hi, rfl⟩ := hX
      exact ⟨_, hM'.2 i hi⟩
    · exact hX.elim
    · have hj : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
      exact ⟨_, hM'.1 j hj⟩
  have key : ∀ X : Node, ∃ c : ℝ≥0, (DefNode D.R.m X → X ≠ .top D.R.m → M.ν X = c • M'.ν X) ∧
      (DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → c = 1) := by
    intro X
    by_cases hX : DefNode D.R.m X ∧ X ≠ .top D.R.m ∧ ∀ j ∈ idx D, X ≠ .top j
    · obtain ⟨hd, hne, hidx⟩ := hX
      refine ⟨1, fun _ _ => ?_, fun _ _ _ => rfl⟩
      rw [one_smul]
      have hMX := hM.vtx X (hdef X hd hne)
      rcases X with ⟨i, j⟩ | i | j
      · obtain ⟨hi, rfl⟩ := hd
        exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (hrow t i hi) (hM'.2 i hi))
      · exact hd.elim
      · have hj : j < D.R.m := lt_of_le_of_ne hd (fun e => hne (by rw [e]))
        have hj' : j ∉ idx D := fun hm => hidx j hm rfl
        simp only [idx, List.mem_range'_1] at hj'
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (hM'.1 0 hj)
        · have e : j = D.R.m - 1 := by omega
          have h2 : 2 ≤ D.R.m := by omega
          subst e
          exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (htop t Φ β hj h2) (hM'.1 _ hj))
    · by_cases hX' : DefNode D.R.m X ∧ X ≠ .top D.R.m
      · obtain ⟨hd, hne⟩ := hX'
        obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V X)
        obtain ⟨K', hK'⟩ := hM'at X hd hne
        haveI := isHaar_of_isAt M X (hM.vtx X (hdef X hd hne))
        haveI := isHaar_of_isAt M' X hK'
        exact ⟨Measure.haarScalarFactor (M.ν X) (M'.ν X), fun _ _ => Measure.isMulLeftInvariant_eq_smul _ _,
          fun h1 h2 h3 => (hX ⟨h1, h2, h3⟩).elim⟩
      · exact ⟨1, fun h1 h2 => (hX' ⟨h1, h2⟩).elim, fun h1 h2 _ => (hX' ⟨h1, h2⟩).elim⟩
  choose x hx using key
  exact ⟨x, fun X h1 h2 => (hx X).1 h1 h2, fun X h1 h2 h3 => (hx X).2 h1 h2 h3⟩
