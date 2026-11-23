import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiGroupOfLocalLatticeMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalLatticeMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem suppAt_conj {V : HSp D} {e : AE D} {y : GA D V} (h : SuppAt e V y) (δ : GA D V) : SuppAt e V (δ * y * δ⁻¹) := by
  have hs : (e + cA D e) • (mt V y - 1) = mt V y - 1 := Matrix.ext fun i j => h i j
  have hδ : mt V δ * mt V δ⁻¹ = 1 := by rw [← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one]
  have key : mt V (δ * y * δ⁻¹) - 1 = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hδ]
  have h2 : (e + cA D e) • (mt V δ * (mt V y - 1) * mt V δ⁻¹) = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasLoc_conj (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m) {y : GA D (G.V (.grid D.R.m j))}
    {g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)} (h : HasLoc t B hj y g)
    (δ : GA D (G.V (.grid D.R.m j))) :
    HasLoc t B hj (δ * y * δ⁻¹) (fun w => locAt B t w.1 j hj δ * g w * (locAt B t w.1 j hj δ)⁻¹) := by
  obtain ⟨e, he, hs, hl⟩ := h
  refine ⟨e, he, suppAt_conj hs δ, fun w => ?_⟩
  change locAt B t w.1 j hj (δ * y * δ⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => locAt B t w.1 j hj δ * z * (locAt B t w.1 j hj δ)⁻¹) (hl w)

theorem conj_rowR' {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} (hy : ∃ f, (toFrame hs hj y).val = diagonal f) (hx : x ∈ rowR hs hj) :
    y * x * y⁻¹ ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have hy' : ∃ f, (toFrame hs hj y⁻¹).val = diagonal f :=
    ⟨Ring.inverse f, by rw [map_inv, Matrix.coe_units_inv, hf, Matrix.inv_diagonal]⟩
  have := conj_rowR hs hj (g := fun _ => 1) hy' hx
  have e1 : GlobalTheory.SplitFlip.diagGL (fun _ => (1 : kˣ)) = (1 : GL (Fin (Γ.rank (Γ.m, j))) k) :=
    Units.ext (by rw [GlobalTheory.SplitFlip.diagGL_val]; exact diagonal_one)
  rwa [e1, mul_one, inv_inv] at this

theorem sgn_diag {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    (c : Fin (Γ.rank (Γ.m, j)) → kˣ) : ∃ f, (toFrame hs hj (GlobalTheory.SplitFlip.diagGL c)).val = diagonal f := by
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact ⟨_, submatrix_diagonal_equiv (fun i => (c i : k)) (frame h)⟩

end GlobalTheory.RowLift

open GlobalTheory.RowLift GlobalTheory.RowRep in

theorem GlobalTheory.RowLift.lift_rowR : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  obtain ⟨C1, hJ⟩ := GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices
  obtain ⟨C2, hB⟩ := GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hx1⟩ := hJ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, hx2⟩ := hB ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  intro s t j hjI hj hj' δ hδ l hl
  obtain ⟨y, hy⟩ := exists_hasLoc hS.core.lev ch.S.B t hj (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹)
  refine ⟨y, hy, ?_⟩
  have hc := hasLoc_conj ch.S.B t hj hy δ
  have hm : ∀ w : locPl ch.G t, locAt ch.S.B t w.1 j hj δ * (sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) *
      (locAt ch.S.B t w.1 j hj δ)⁻¹ ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj' := fun w =>
    conj_rowR' one_le_sLen hj' (locAt_tilt ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' hδ)
      (conj_rowR' one_le_sLen hj' (sgn_diag one_le_sLen hj' _) (hl w))
  unfold rowGrp
  split_ifs with h1 h2
  · exact hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' _
      (by have := (idx_le hjI); omega) _ _ hc hm
  · exact hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' h2 _ _ hc hm
  · exfalso; have := idx_le hjI; omega
