import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem pureTensor_oppArgs_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) (w : Pl D.host.E) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid G t w).rank b.tgt)) (Fin ((locGrid G t w).rank b.src)) (Kw w) → ℂ) (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank) (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank), (locGrid G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ (oppArgs t B w x y) = (∏ i : Fin D.R.m, φ (.ex i D.R.m) (B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((x i).map fun a => cpt w (toEAf D a)))) * ∏ j : Fin D.R.m, φ (.theta D.R.m j) (B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ ((y j).map fun a => cpt w (toEAf D a))) := by
  intro D T L sc G t B w φ x y
  show ((GlobalTheory.SplitFlip.oppositePath D.R.m).map fun b => φ b (oppArgs t B w x y b)).prod = _
  simp only [GlobalTheory.SplitFlip.oppositePath, List.map_append, List.prod_append, List.map_reverse,
    List.prod_reverse, List.map_map]
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.map_map, ← Fin.prod_univ_def, ← Fin.prod_univ_def]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_ <;> simp [oppArgs]

theorem flipFin_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t Φ e τ φ hloc hfac n xw φw hexp x y
  by_cases hh : (∀ i, IsHalf e (x i)) ∧ ∀ j, IsHalf e (y j)
  · rw [hfac x y hh.1 hh.2, ← Finset.prod_coe_sort]
    simp_rw [hexp, pureTensor_oppArgs_local]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh.1, hh.2, ↓reduceIte, Finset.prod_mul_distrib]
    rw [mul_assoc]
    congr 2 <;> exact Finset.prod_comm
  · rw [not_and_or] at hh
    rcases hh with hh | hh <;> simp only [not_forall] at hh <;> obtain ⟨k, hk⟩ := hh
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).1 k (x k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).1 k).1.1 (x k) hne)
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).2 k (y k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).2 k).1.1 (y k) hne)
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)

end GlobalTheory.LocAsm
