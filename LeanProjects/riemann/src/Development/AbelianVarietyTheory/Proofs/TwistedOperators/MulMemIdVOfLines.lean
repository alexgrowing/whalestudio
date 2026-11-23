import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimAtOfMonoId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem pX_xLast_castSucc {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k l : Fin σ) :
    (dW.pX ⬝ xLast dW z) k l.castSucc = (1 : Mx D σ σ) k l := by
  rw [← dW.pX_jX]
  simp only [Matrix.mul_apply, SuppShift.xLast_castSucc]

theorem pX_xLast_last {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k : Fin σ) :
    (dW.pX ⬝ xLast dW z) k (Fin.last σ) = 0 := by
  have h : (dW.pX ⬝ xLast dW z) k (Fin.last σ) = ((dW.pX ⬝ dW.j0) *ᵥ ratV z) k := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, SuppShift.xLast_last]
  rw [h, dW.pX_j0, Matrix.zero_mulVec, Pi.zero_apply]

theorem pX_xLast_mul_apply {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    (N : Mx D (σ + 1) (σ + 1)) (k : Fin σ) (j : Fin (σ + 1)) :
    (dW.pX ⬝ (xLast dW z ⬝ N)) k j = N k.castSucc j := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_castSucc, pX_xLast_last, zero_mul, add_zero]
  simp only [pX_xLast_castSucc, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem psiE_idem_entry {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {σ : ℕ}
    (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (LV : Lat V) (LW : Lat W) (LW₀ : Lat W₀)
    {v : Pl D} (hm : MonoAt dW LW LW₀ v) (hp : PrimAt ψ dV LV v) (hc : ColsAt dV (xLast dW z) LV LW v)
    (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ latA W LW (· = v))
    (i j : Fin (σ + 1)) (hij : j.1 = i.1 + 1) : psiE ψ (idem D (· = v) * N i j) = 1 := by
  obtain ⟨-, -, -, -, -, -, f7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hiσ : i.1 < σ := by have := j.2; omega
  set i' : Fin σ := ⟨i.1, hiσ⟩ with hi'
  have hii : i'.castSucc = i := Fin.ext rfl
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : ∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (s * a) ∈ latV V LV (· = v) := by
    intro a ha
    have haA : a ∈ idAt D (· = v) := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul dV ha
    have h1 := hY _ ha
    rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
    have hb : N i j * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ haA
    have h2 : colMul (xLast dW z) i (N i j * a) ∈ latA W LW (· = v) := by
      refine (f7 W LW _).2 ⟨fun k => Ideal.mul_mem_right _ _ hb, fun t ht => ?_⟩
      have h3 := ((f7 W LW _).1 h1).2 t ht
      have h4 := ((hm _).1 h3).1 i'
      have e1 : (dW.pX *ᵥ (t • colMul (xLast dW z ⬝ N) j a)) i' = t * (a * N i j) := by
        rw [Matrix.mulVec_smul, PsiUnit.mulVec_colMul, Pi.smul_apply, smul_eq_mul, colMul,
          pX_xLast_mul_apply dW z N, hii]
      rw [e1] at h4
      convert h4 using 1
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, colMul, ← hii, SuppShift.xLast_castSucc]
      ring
    have h5 := (hc i (N i j * a) hb).2 h2
    have e2 : s * a = N i j * a := by
      rw [hsdef, mul_comm (idem D (· = v)), mul_assoc, (mem_idAt_iff _ a).1 haA]
    rwa [e2]
  have h6 := (hp i j hij s hs).1 key (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_mem_idV_of_lines {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ)
    (z : Fin W₀.rank → D.host.E) (LV : Lat V) (A : AddSubgroup (Fin W.rank → AE D)) (𝔟V 𝔟W : GlobalTheory.SeeSaw.FI D) {v : Pl D}
    (k : Fin σ) (j : Fin (σ + 1)) (hV : ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, colMul dV.jX j a ∈ latV V LV (· = v))
    (hW : ∀ y ∈ A, (dW.pX *ᵥ y) k ∈ GlobalTheory.SeeSaw.idV 𝔟W v) (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ A) :
    ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, N k.castSucc j * a ∈ GlobalTheory.SeeSaw.idV 𝔟W v := by
  intro a ha
  have h1 := hY _ (hV a ha)
  rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
  have h2 := hW _ h1
  rwa [PsiUnit.mulVec_colMul, colMul, pX_xLast_mul_apply dW z N k j, mul_comm] at h2

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem span_neg (x : D.host.E) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-x) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x :=
  (FractionalIdeal.spanSingleton_eq_spanSingleton).2 ⟨-1, by simp⟩

theorem line_ratio (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    I * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) *
      ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1 + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [pow_succ x (k + 1), ← FractionalIdeal.spanSingleton_mul_spanSingleton, pow_succ 𝔞' (k + 1)]
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact pow_ne_zero _ hx
  have h2 : 𝔞' ^ (k + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  have h3 : 𝔞 ^ n ≠ 0 := pow_ne_zero _ h𝔞
  field_simp

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

variable {D : D7}

theorem line_ratio' (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) * I *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1 + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv]
  rw [← line_ratio I 𝔞 𝔞' h𝔞 h𝔞' x hx n k]
  ring

end GlobalTheory.UniStepFB
