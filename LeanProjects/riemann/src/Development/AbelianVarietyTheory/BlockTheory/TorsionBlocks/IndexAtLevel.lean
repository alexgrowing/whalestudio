import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

open Formalism.BasicNotions Formalism.MainNotions

variable (D : D7) (u : D.what₂.Word)

def rankAll : ℕ := Module.finrank D.what₂.LL (LT.Vl D u 0)

def rankRam : ℕ := Module.finrank D.what₂.LL (D.fm u).ramSub

def lengthN_vw (w : D.what₂.places.Pl) : ℕ∞ :=
  Module.length (LT.Ow D w) (↥(LT.Sram D u w) ⧸ (LT.Nlam D u w).comap (LT.Sram D u w).subtype)

def IsScaledU (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (g : (D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub) : Prop :=
  ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (g x : LT.Vl D u 0) =
    (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) •
      LT.Uop D u 0 v ((D.fm u).emb 0 (x : LT.Vl D u 0))

def topSize (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : ℝ :=
  ((D.fm u).aTop ((D.fm u).tauOf w v) : ℝ) / (D.R.k : ℝ) + 2 * (Wtau D u ((D.fm u).tauOf w v) : ℝ)

def boundFine_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * ∑ v ∈ LT.VVT D u w,
    ((rankAll D u : ℝ) * topSize D u w v + ((D.R.k : ℝ) - 1) * (rankRam D u : ℝ))

def boundCoarse_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w, (topSize D u w v + (D.R.k : ℝ) - 1)

def boundQuoted_vp (w : D.what₂.places.Pl) : ℝ :=
  (D.R.m : ℝ) * (rankAll D u : ℝ) * ∑ v ∈ LT.VVT D u w,
    (topSize D u w v + (D.R.k : ℝ) + ((D.fm u).bTop ((D.fm u).tauOf w v) : ℝ))

def IndexAtPlace (w : D.what₂.places.Pl) : Prop :=
  LT.Nlam D u w ≤ LT.Sram D u w ∧
  ∃ (g : (D.mem u).A.vT → ((D.fm u).ramSub →ₗ[D.what₂.LL] (D.fm u).ramSub))
    (n : (D.mem u).A.vT → ℤ) (l : ℕ),
    (∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v) ∧
      D.what₂.places.val w (LinearMap.det (g v)) = ((n v : ℤ) : WithTop ℤ)) ∧
    lengthN_vw D u w = (l : ℕ∞) ∧
    (l : ℤ) = (D.R.m : ℤ) * ∑ v ∈ LT.VVT D u w, n v ∧
    (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * boundFine_vp D u w ∧
    boundFine_vp D u w ≤ boundCoarse_vp D u w

def IndexAtLevel : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → IndexAtPlace D u w

def IndexAtLevelKnown : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    LT.Nlam D u w ≤ LT.Sram D u w ∧
    ∃ l : ℕ, lengthN_vw D u w = (l : ℕ∞) ∧
      (l : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * boundQuoted_vp D u w

def IndexAtLevelFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.L x i).TuGe → ∀ u, IndexAtLevel (Fm.D x i) u

theorem boundFine_le_boundCoarse (w : D.what₂.places.Pl) : boundFine_vp D u w ≤ boundCoarse_vp D u w := by
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have h3 := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hr : (rankRam D u : ℝ) ≤ (rankAll D u : ℝ) := by
    haveI : Module.Finite D.what₂.LL (LT.Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
    unfold rankRam rankAll
    exact_mod_cast Submodule.finrank_le _
  unfold boundFine_vp boundCoarse_vp
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  nlinarith

end GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

end
