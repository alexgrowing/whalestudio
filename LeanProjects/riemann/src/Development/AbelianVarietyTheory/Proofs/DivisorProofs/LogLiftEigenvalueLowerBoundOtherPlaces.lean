import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowOff

theorem le_log_of_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) (m : ℂ) (lam B : ℝ)
    (hlam : 0 < lam) (hm : m ≠ 0) (hg : ⟪w, w⟫_ℂ = ((lam : ℝ) : ℂ) * m) (hl : Real.exp B * m.re ≤ ‖w‖ ^ 2) :
    B ≤ Real.log lam := by
  rw [inner_self_eq_norm_sq_to_K] at hg
  have hg' : ((‖w‖ ^ 2 : ℝ) : ℂ) = ((lam : ℝ) : ℂ) * m := by rw [Complex.ofReal_pow]; exact hg
  have hre := congrArg Complex.re hg'
  have him := congrArg Complex.im hg'
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  have him0 : m.im = 0 := by
    rcases mul_eq_zero.mp him.symm with h | h
    · exact absurd h hlam.ne'
    · exact h
  have hre0 : m.re ≠ 0 := fun h => hm (Complex.ext h him0)
  have hpos : 0 < m.re := by
    have : 0 ≤ lam * m.re := by rw [← hre]; positivity
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right (by linarith) hlam) (Ne.symm hre0)
  rw [Real.le_log_iff_exp_le hlam]
  have : Real.exp B * m.re ≤ lam * m.re := by rw [← hre]; exact hl
  exact le_of_mul_le_mul_right this hpos

theorem partAt_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j p v) :
    R.PartAt F j p v ↔ ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL,
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x x ≠ 0 := Iff.rfl

set_option maxHeartbeats 4000000 in

theorem l6m_le_log_lam3_other_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hC hph hP hG hL hb j p v hv
  by_cases hPA : R.PartAt F j p v
  · rw [partAt_iff, GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hPA
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hG hb ⊢
    obtain ⟨x, hx, hne⟩ := hPA
    exact (hb j).trans (le_log_of_inner_eq _ _ _ _ (hP.2 j A3.A.μ0 p v) hne (hG j v hv p x hx x) (hL j v hv x))
  · rw [hC.scal.abs j p v hv hPA, Real.log_exp]

end GlobalTheory.LowOff
