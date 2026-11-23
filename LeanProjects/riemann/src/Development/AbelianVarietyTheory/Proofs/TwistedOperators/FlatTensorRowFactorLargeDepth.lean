import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm
open GlobalTheory.SplitFlip

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem moved_pureTensor_eq_mul (G : Grid k) (keep : Bool) (g : G.VertexGroup)
    (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (z : G.Args) :
    moved G keep g (G.lines₂ (oppositePath G.m) φ) z =
      moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ)) z *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (z (.ex i G.m)) := by
  have h1 : ((List.range G.m).map fun i => φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))) =
      (List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m)) := by
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨ha, hb⟩ := hg i (List.mem_range.1 hi)
    simp only [Grid.moveArgs, Edge.src, Edge.tgt, ha, hb, map_one, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one]
  have h2 : ((List.range G.m).map fun i => exOne φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))).prod = 1 := by
    simp
  simp only [moved, Grid.pathAct, Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_map,
    Function.comp_def]
  rw [h1, h2]
  show _ = _ * ((List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m))).prod
  simp only [exOne_theta, List.map_reverse]
  ring

theorem moved_exOne_fill (G : Grid k) (hs : 1 ≤ G.s) (keep : Bool) (g : G.VertexGroup) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y y' : RowArgs G)
    (e : Vars G) :
    moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y e) =
      moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y' e) := by
  simp only [moved, Grid.pathAct, Grid.lines₂]
  congr 3
  refine List.map_congr_left fun b _ => ?_
  cases b <;> rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_pureTensor (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) φ)) x y =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ))) x 0 *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ := by
  unfold flatTensor flatIntegrand
  rw [← integral_mul_const]
  congr 1
  funext e
  rw [moved_pureTensor_eq_mul G keep g hg φ, moved_exOne_fill G hs keep g _ φ x y 0 e]
  simp only [fill_ex]
  ring

end General

theorem Reps.elt_row {k : Type} [Field k] {G : Grid k} {hs : 1 ≤ G.s} {J : G.Level} (ρ : Reps hs J)
    (β : Cosets hs J) : ∀ i < G.m, ρ.elt β (i, G.m) = 1 ∧ ρ.elt β (i + 1, G.m) = 1 := by
  intro i hi
  refine ⟨dif_neg (by simp only; omega), ?_⟩
  by_cases h : i + 1 = G.m
  · have key : ∀ j (hj : j = i + 1), ρ.elt β (G.m, j) = 1 := by
      intro j hj
      subst hj
      rw [Reps.elt, onColumn_apply]
      exact dif_neg (by omega)
    rw [h]
    exact key G.m h.symm
  · exact dif_neg (by simp only; omega)

theorem flatTensor_rowFactor : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t β w φ _ u y
  refine (flatTensor_moved_pureTensor (locGrid ch.G t w.1) one_le_sLen _ _ _ _ (Reps.elt_row _ _) φ _ _).trans ?_
  congr 1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GridChoice.rowAt]
  rw [dif_pos (show (i : ℕ) < D.R.m from i.2)]
  rfl

end GlobalTheory.LocAsm
