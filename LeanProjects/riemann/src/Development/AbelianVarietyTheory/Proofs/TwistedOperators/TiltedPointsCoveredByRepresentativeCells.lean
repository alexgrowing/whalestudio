import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInvStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem eltAt {k : Type} [Field k] {Gr : GlobalTheory.SplitFlip.Grid k} {hs : 1 ≤ Gr.s} {J : Gr.Level} (ρ : Reps hs J)
    (β : Cosets hs J) (i : ℕ) (hi : i < Gr.m - 2) : ρ.elt β (Gr.m, i + 1) = ρ.rep ⟨i, hi⟩ (β ⟨i, hi⟩) := by
  rw [Reps.elt, onColumn_apply]
  simp only [dif_pos hi]

set_option maxHeartbeats 1600000 in

theorem cover_at : Big fun ch => ∀ s, CoverAt ch s := by
  refine big_mono (fun {D} _ _ _ _ _ _ _ _ _ _ _ ch h => ?_) (Big.and GlobalTheory.T.rowTest_mem_latticeStabilizer_of_localMatrices GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements)
  obtain ⟨h5, h7⟩ := h
  classical
  intro s t b hb p hp
  have hidx : ∀ i : ℕ, i < D.R.m - 2 → i + 1 ∈ idx D := fun i hi => by
    simp only [idx, List.mem_range'_1]; omega
  choose r hr a ha δ x g hδ hx k hk hpe using hp
  let β : CosFam ch.G t := fun w i => DoubleCoset.mk _ _
    ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) (hidx i i.2) (by have h : (i : ℕ) < D.R.m - 2 := i.2; omega) w)
  refine ⟨β, fun j hj => ?_⟩
  have hj1 : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := by simpa [idx, List.mem_range'_1] using hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m - 2 := by omega
  have hjm : i + 1 ≤ D.R.m := by omega
  have hj' : i + 1 < D.R.m := by omega
  obtain ⟨-, hb2⟩ := hb β
  obtain ⟨δ', r', hδ', hr', hfin, a₀, ha₀, hab⟩ := hb2 (i + 1) hj hjm
  have key : ∀ w : locPl ch.G t, ∃ l : GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i + 1))) (Kw w.1), l ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := i + 1) hj' ∧
      ∃ κ ∈ givenLevel ch.G t w.1 (D.R.m, i + 1),
        (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) =
          l * ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) hj hjm w) * κ := by
    intro w
    have e1 : (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) = (repsAt ch.G t w.1).rep ⟨i, hi⟩ (β w ⟨i, hi⟩) :=
      eltAt (repsAt ch.G t w.1) (β w) i hi
    have e2 := (repsAt ch.G t w.1).mk_rep ⟨i, hi⟩ (β w ⟨i, hi⟩)
    rw [e1]
    obtain ⟨l, hl, κ, hκ, e⟩ := (DoubleCoset.eq _ _ _ _).1 e2.symm
    exact ⟨l, hl, κ, hκ, e⟩
  choose l hl κ hκ hrep using key
  obtain ⟨y, hy, hyR⟩ := h7 s t (i + 1) hj hjm hj' (δ (i + 1) hj hjm) (hδ _ _ _) (fun w => (l w)⁻¹)
    fun w => inv_mem (hl w)
  have h1 := GlobalTheory.T.hasLocalLatticeMatrices_mul t ch.S.B hjm y r' _ _ hy hr'
  have h2 := GlobalTheory.T.hasLocalLatticeMatrices_inv t ch.S.B hjm (y * r') _ h1
  have hz := GlobalTheory.T.hasLocalLatticeMatrices_mul t ch.S.B hjm ((y * r')⁻¹) (x (i + 1) hj hjm) _ _ h2 (hx (i + 1) hj hjm)
  have hfun : (fun w => ((sgnAt ch.G t s w.1 (i + 1) * (l w)⁻¹ * (sgnAt ch.G t s w.1 (i + 1))⁻¹) *
      (sgnAt ch.G t s w.1 (i + 1) * (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1)))⁻¹ * g (i + 1) hj hjm w) =
      fun w => (κ w)⁻¹ := by
    funext w
    rw [hrep w]
    group
  rw [hfun] at hz
  set z := (y * r')⁻¹ * x (i + 1) hj hjm with hzdef
  have hzl : z ∈ latGrp ch.G (i + 1) := h5 t (i + 1) (by omega) hjm _ _ hz fun w => inv_mem (hκ w)
  have htilt : δ (i + 1) hj hjm = δ' := GlobalTheory.T.isRowFlagTilt_unique ch.G hj' _ _ (hδ _ _ _) hδ'
  have hyf : y ∈ GfC _ := GlobalTheory.T.mem_finitePoints_of_hasLocalLatticeMatrices t ch.S.B hjm _ _ hy
  set Y := δ (i + 1) hj hjm * y * (δ (i + 1) hj hjm)⁻¹ with hY
  have hYf : Y ∈ GfC _ := by
    rw [GfC, MonoidHom.mem_ker] at hyf ⊢
    rw [hY, map_mul, map_mul, hyf, mul_one, map_inv, mul_inv_cancel]
  have hcomm : a (i + 1) hj hjm * Y = Y * a (i + 1) hj hjm :=
    (GlobalTheory.AdelicSplit.adelic_split D _).2.2.1 _ (ha _ _ _) _ hYf
  refine ⟨r (i + 1) hj hjm * Y, mul_mem (hr _ _ _) hyR, a (i + 1) hj hjm * a₀, mul_mem (ha _ _ _) ha₀,
    z * k (i + 1) hj hjm, mul_mem hzl (hk _ _ _), ?_⟩
  have hxz : x (i + 1) hj hjm = y * r' * z := by rw [hzdef, mul_inv_cancel_left]
  rw [hpe (i + 1) hj hjm, hxz, show r (i + 1) hj hjm * Y * (a (i + 1) hj hjm * a₀) * b β (i + 1) * (z * k (i + 1) hj hjm) =
    r (i + 1) hj hjm * (a (i + 1) hj hjm * Y) * (a₀ * b β (i + 1)) * z * k (i + 1) hj hjm by
      rw [hcomm]; simp only [mul_assoc], hab, ← htilt, hY]
  simp only [mul_assoc, inv_mul_cancel_left]

end GlobalTheory.RowVal
