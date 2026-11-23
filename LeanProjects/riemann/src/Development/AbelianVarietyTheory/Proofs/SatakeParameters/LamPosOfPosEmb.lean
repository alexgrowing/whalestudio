import Mathlib
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.PlaceAbove

theorem involution_conj (D : D7) (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

theorem posArg_eq_self (D : D7) {n : ℕ} (s : Fin n) (x : D.host.E) :
    (if Even s.val then (if IsOddPos s then D.host.conj x else x)
      else sigD D (if IsOddPos s then D.host.conj x else x)) = x := by
  by_cases hs : s.val % 2 = 1
  · have hodd : IsOddPos s := hs
    have hne : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    rw [if_neg hne, if_pos hodd, involution_conj]
  · have hodd : ¬ IsOddPos s := hs
    have hev : Even s.val := by rw [Nat.even_iff]; omega
    rw [if_pos hev, if_neg hodd]

end GlobalTheory.TwU.PlaceAbove

open GlobalTheory.TwU.PlaceAbove in

theorem GlobalTheory.TwU.lamPos_of_posEmb : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (e : D.what₂.LL →+* X.G.Kf), (∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (e z) = lam ⟨D.what₂.embLL z, hz⟩) → (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E), e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = X.G.P.ι v ((X.G.P.σ v ^ s.val) (ρ v x))) → LamPos X E pos lam ρ := by
  intro p _ X E D pos lam ρ e hK hpos
  intro v s x
  have h1 := hpos v s (if IsOddPos s then D.host.conj x else x)
  rw [posArg_eq_self D s x] at h1
  have hz := embLL_mem_alg D (tEL D (pos ⟨v, s⟩) x)
  have h2 := hK (tEL D (pos ⟨v, s⟩) x) hz
  have he : Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x = D.what₂.embLL (tEL D (pos ⟨v, s⟩) x) := (tEL_emb D (pos ⟨v, s⟩) x).symm
  have hL : Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = lam ⟨D.what₂.embLL (tEL D (pos ⟨v, s⟩) x), hz⟩ := by
    unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dif_pos (he ▸ hz)]
    congr 1
    exact Subtype.ext he
  show Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [hL, ← h2, h1]
  rfl
