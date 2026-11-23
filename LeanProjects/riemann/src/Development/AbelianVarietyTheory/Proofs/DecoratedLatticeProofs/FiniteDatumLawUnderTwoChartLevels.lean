import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.LevDat

set_option synthInstance.maxHeartbeats 200000 in

theorem half_nsmul {D : D7} {m n : ℕ} (e : AE D) (v : Mx D m n) (h : IsHalf e v) (k : ℕ) : IsHalf e (k • v) :=
  fun r c => by
    change e * (k • v r c) = k • v r c
    rw [nsmul_eq_mul, mul_left_comm, h r c, ← nsmul_eq_mul]

theorem sb_step {Y : Type} [AddCommGroup Y] (Λ : AddSubgroup Y) (hf : Y → Prop) (Φ : Y → ℂ) (k : ℕ)
    (hinv : ∀ u ∈ Λ, hf u → ∀ t, Φ (t + k • u) = Φ t) (k' : ℕ) (v : Y) (hv : v ∈ Λ) (hh : hf (k' • v)) (t : Y) :
    Φ (t + (k * k') • v) = Φ t := by
  have h := hinv (k' • v) (AddSubgroup.nsmul_mem Λ hv k') hh t
  rw [← mul_smul] at h
  exact h

set_option maxHeartbeats 1000000 in

theorem levDat_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z, IsHalf A.e z → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ z := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy z hz
  obtain ⟨hs1, k1, hk1, hinv1, hsup1⟩ := GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hΦ' := hΦ
  obtain ⟨hs2, k2, hk2, hinv2, hsup2⟩ := hΦ'
  obtain ⟨w, v, hv, hvh, hzw⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom _ _ A.e _ hA.idem (k1 * k2) (Nat.mul_pos hk1 hk2) z hz
  subst hzw
  have e1 := sb_step _ (IsHalf A.e) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) k1 hinv1 k2 v hv
    (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  have e2 := sb_step _ (IsHalf A.e) Φ k2 hinv2 k1 v hv (half_nsmul _ _ hvh _) (w.map fun r => A.e * incA (I.rec7 l Z) r)
  rw [mul_comm k2 k1] at e2
  beta_reduce at e1
  rw [e1, e2]
  exact GlobalTheory.T.finiteDatumLaw_rationalPoints_half I hI hP l Z u a Ch A hA i hi α γ Φ hΦ p hp κ κ' x y hx hy w

end GlobalTheory.LevDat
