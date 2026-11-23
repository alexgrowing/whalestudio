import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.EigenSplitStrings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings GlobalTheory.DownLift

namespace GlobalTheory.PtStringTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem aPl_last_pos (i : Fin D.R.m) (τ : D.what₂.Tau) : 0 < aPl D i (D.R.k + i) τ (D.R.k + i - 1) := by
  have hk : 1 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    omega
  have hn : D.R.k + (i : ℕ) - 1 < D.R.k + (i : ℕ) := by omega
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k + (i : ℕ) - 1) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    ext
    simp only
    omega
  have hc : ((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1 = ((D.R.k + (i : ℕ) : ℕ) : ℚ) := by
    have : D.R.k + (i : ℕ) - 1 + 1 = D.R.k + (i : ℕ) := by omega
    exact_mod_cast this
  have hgap := (D.hc τ).gap_be i
  have h1 : (1 : ℚ) ≤ -(D.hc τ).b i + (D.hc τ).e i
      - (((D.R.k + (i : ℕ) : ℕ) : ℚ) - (((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    linarith
  have h2 := Int.floor_pos.2 h1
  unfold aPl
  rw [if_pos hn, hlam]
  omega

theorem str_le_str_add_two (q : ℕ) (z : ℂ) (n : ℕ) : str q z n ≤ str q z (n + 2) := by
  have hsub : (Multiset.range n).map Nat.succ ≤ Multiset.range (n + 2) := by
    rw [Multiset.le_iff_subset ((Multiset.nodup_range n).map Nat.succ_injective)]
    intro a ha
    simp only [Multiset.mem_map, Multiset.mem_range] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simp only [Multiset.mem_range]
    omega
  unfold str
  calc (Multiset.range n).map (fun k : ℕ => z * (q : ℂ) ^ (((n : ℂ) - 1) / 2 - (k : ℂ)))
      = ((Multiset.range n).map Nat.succ).map
          (fun k : ℕ => z * (q : ℂ) ^ ((((n + 2 : ℕ) : ℂ) - 1) / 2 - (k : ℂ))) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun k _ => ?_
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        congr 2
        push_cast
        ring
    _ ≤ _ := Multiset.map_le_map hsub

end GlobalTheory.PtStringTest

end
