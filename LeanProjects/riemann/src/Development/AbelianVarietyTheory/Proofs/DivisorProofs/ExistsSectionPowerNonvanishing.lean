import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowSecNonzero

def oneSec {Y : Scheme.{0}} (H : LB Y) : LB.Sec (pw H ((0 : ℕ) : ℤ)) where
  f := fun _ => 1
  compat := fun k l => by
    change rs Y (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) 1 =
      (H.g k l ^ ((0 : ℕ) : ℤ)).val * rs Y (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) 1
    simp

def powSec {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (u : ℕ) : LB.Sec (pw H (u : ℤ)) :=
  Nat.rec (motive := fun u : ℕ => LB.Sec (pw H (u : ℤ))) (oneSec H)
    (fun u σ => GlobalTheory.VeryAmpleGrowth.mulPw s u σ) u

theorem powSec_f {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι) :
    ∀ u : ℕ, (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ u
  | 0 => by simp [powSec, oneSec]; rfl
  | u + 1 => by
    change s.f k * (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ (u + 1)
    rw [powSec_f s k u, pow_succ, mul_comm]

theorem exists_pw_sec_nonzero : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  intro Y D J s i x hx u
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨powSec (s i) u, TopologicalSpace.Opens.mem_iSup.2 ⟨k₀, ?_⟩⟩
  have e := powSec_f (s i) k₀ u
  change x ∈ Y.basicOpen (show Γ(Y, D.U k₀) from (powSec (s i) u).f k₀)
  rw [e]
  cases u with
  | zero =>
    rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact Y.basicOpen_le _ hk₀
  | succ n => rw [Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]; exact hk₀

end GlobalTheory.PowSecNonzero
