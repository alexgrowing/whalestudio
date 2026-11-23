import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FixedIod
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalRingCardinality.FactDelDualNabla

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section HostLemmas

variable {R : Ranks} (H : Host R)

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h := by
  unfold Host.sigmaOf
  exact map_mul _ g h

theorem sigmaOf_one : H.sigmaOf 1 = 1 := by
  unfold Host.sigmaOf
  exact map_one _

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g := by
  unfold Host.sigmaOf
  exact MulEquiv.apply_symm_apply _ _

theorem sigmaOf_sqrt_neg (g : R.GG) (h : g.1.2 = -1) : H.sigmaOf g H.sqrtMinusD = -H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sigmaOf_sqrt_pos (g : R.GG) (h : g.1.2 = 1) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem emb_sigmaOf (g h : R.GG) (x : H.E) : H.emb g (H.sigmaOf h x) = H.emb (g * h) x := by
  unfold Host.emb
  rw [sigmaOf_mul]
  rfl

end HostLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Polynomial
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section KurLemmas

variable {p : ℕ} [Fact p.Prime]

theorem mem_Kur_of_pow {x : ℂ_[p]} (n : ℕ) (hn : 0 < n) (hd : ¬ p ∣ n) (hx : x ^ n = 1) : x ∈ MaximalUnramifiedExtension p :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hd, hx⟩)

variable {R : Ranks} (H : Host R) (J : H.E →+* ℂ_[p])

end KurLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section Fixed

variable {R : Ranks} (H : Host R)

def sInv (R : Ranks) : R.GG := ((1, -1), 1)

end Fixed

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.MainNotions.G (plGG)

theorem embT_tauPl (D : D7) (z : Bool × HH D) : TaylorLogMetric.embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold TaylorLogMetric.embT tauPl
  rw [Equiv.apply_symm_apply]

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem tauSg_tauPl (D : D7) (b : Bool) (t : HH D) : TaylorLogMetric.tauSg D (tauPl D (b, t)) = tauPl D (!b, t) := by
  have hm : plGG D (b, t) * TaylorLogMetric.sgm D = plGG D (!b, t) := by
    cases b <;> refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, TaylorLogMetric.sgm]
  have hmem : (D.eTau (tauPl D (b, t)) : D.R.GG) * TaylorLogMetric.sgm D ∈ D.R.Psi := by
    rw [eTau_tauPl, hm]; exact plGG_mem_Psi D _
  rw [show TaylorLogMetric.tauSg D (tauPl D (b, t)) = D.eTau.symm ⟨_, hmem⟩ from dif_pos hmem]
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  simp only [eTau_tauPl, hm]

theorem inertia_pairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧
    cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧
    Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧
    (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧
    (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧
    (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧
    ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧
      TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  intro D p _ hp ι
  have hp2 : p ≠ 2 := by rw [hp]; exact D.host.hypOdd.2.2.2.2
  have hpq : D.host.q ≠ p := by rw [hp]; exact D.host.hypOdd.2.2.1
  refine ⟨D.host.conj.toRingEquiv, (D.host.sigmaOf (sInv D.R)).toRingEquiv, D.host.sqrtMinusD, fun y => rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, tauPl_bij D, fun t => ⟨tauSg_tauPl D false t, tauSg_tauPl D true t⟩⟩
  · rw [sqrt_sq, hp]
  · exact sigmaOf_sqrt_neg D.host (D.R.cc) rfl
  · exact sigmaOf_sqrt_neg D.host (sInv D.R) rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (sInv D.R) y) = y
    rw [← AlgEquiv.mul_apply, ← sigmaOf_mul]
    have : sInv D.R * sInv D.R = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [sInv]
    rw [this, sigmaOf_one]
    rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y) = D.host.sigmaOf (D.R.cc) (D.host.sigmaOf (sInv D.R) y)
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← sigmaOf_mul, ← sigmaOf_mul, mul_comm]
  · intro z z' h
    have h' : ∀ x, D.host.φ₀ (D.host.sigmaOf (plGG D z) x) = D.host.φ₀ (D.host.sigmaOf (plGG D z') x) := fun x => by
      have := RingHom.congr_fun h x
      simp only [embT_tauPl] at this
      exact this
    have hs : D.host.sigmaOf (plGG D z) = D.host.sigmaOf (plGG D z') :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (h' x)
    have hg : plGG D z = plGG D z' := by
      unfold Host.sigmaOf at hs
      exact (D.host.gal).symm.injective hs
    apply (tauPl_bij D).1
    unfold tauPl
    congr 1
    exact Subtype.ext hg
  · intro τ ρ
    change D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) D.host.sqrtMinusD) =
      D.host.φ₀ (D.host.sigmaOf (D.eTau ρ : D.R.GG) D.host.sqrtMinusD)
    rw [sigmaOf_sqrt_pos D.host _ (D.eTau τ).2, sigmaOf_sqrt_pos D.host _ (D.eTau ρ).2]
  · intro t y
    change D.host.emb _ y = D.host.emb _ (D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y))
    rw [eTau_tauPl, eTau_tauPl, emb_sigmaOf, emb_sigmaOf]
    have hg : plGG D (false, t) * sInv D.R * D.R.cc = plGG D (true, t) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, sInv, Formalism.HC.Frame.cc, c0]
    rw [hg]
  · intro τ y hy
    have hy' : D.host.sigmaOf (sInv D.R) y = y := hy
    exact UpperTheory.Ram.image_mem_of_fixed_iod D.host ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D τ)) (MaximalUnramifiedExtension p)
      (fun z hz => mem_Kur_of_pow _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos)
        (by rw [hp]; exact D.host.toHostRaw.d_not_dvd_QSq) hz) y hy'

end GlobalTheory.InertiaPairs
