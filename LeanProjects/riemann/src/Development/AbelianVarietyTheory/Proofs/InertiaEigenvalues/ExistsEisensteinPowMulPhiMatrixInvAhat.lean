import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem E_pow_mem_RpiE (N : ℕ) : E K l e ^ N ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (pow_mem (E_mem l e (A O K)) N))

theorem E_mem_RpiE : E K l e ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (E_mem l e (A O K)))

theorem hat_E_pow (N : ℕ) :
    hat O l e (E K l e ^ N) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N := by
  induction N with
  | zero => simpa using (hat_coe (O := O) (K := K) l e 1).trans (map_one _)
  | succ n ih =>
    rw [pow_succ, hat_mul l e (E_pow_mem_RpiE n) E_mem_RpiE, ih, hat_E, pow_succ]

theorem main [NeZero a] (P : PhiMod O K l e a ι) :
    ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e), ∀ τ j i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i) := by
  choose n hn using fun p : ZMod a × ι × ι => mem_away.1 (P.mxInv_mem p.1 p.2.1 p.2.2)
  have hN : ∀ p : ZMod a × ι × ι, E K l e ^ Finset.univ.sup n * P.mxInv p.1 p.2.1 p.2.2 ∈ A O K := by
    intro p
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ p))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn p)
  refine ⟨Finset.univ.sup n, fun τ j i => ofA O K l e ⟨_, hN (τ, j, i)⟩, fun τ j i => ?_⟩
  rw [← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P
  exact main P
