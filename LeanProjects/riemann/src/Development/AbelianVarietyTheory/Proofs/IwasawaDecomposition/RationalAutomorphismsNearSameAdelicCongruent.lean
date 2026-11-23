import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

theorem entries_le_of_add_mul {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) K) (c : WithZero (Multiplicative ℤ)) (hA : ∀ r s, v (A r s) < 1)
    (h : ∀ r s, v ((D + A * D) r s) ≤ c) (r s : Fin n) : v (D r s) ≤ c := by
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v (D p.1 p.2)) ⟨(r, s), Finset.mem_univ _⟩
  refine (hmax (r, s) (Finset.mem_univ _)).trans ?_
  by_cases hμ : v (D p.1 p.2) = 0
  · rw [hμ]; exact zero_le'
  have hlt : v ((A * D) p.1 p.2) < v (D p.1 p.2) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ hμ fun k _ => ?_
    rw [map_mul]
    calc v (A p.1 k) * v (D k p.2) ≤ v (A p.1 k) * v (D p.1 p.2) :=
          mul_le_mul_right (hmax (k, p.2) (Finset.mem_univ _)) _
      _ < 1 * v (D p.1 p.2) := mul_lt_mul_of_pos_right (hA p.1 k) (zero_lt_iff.2 hμ)
      _ = v (D p.1 p.2) := one_mul _
  have e := Valuation.map_add_eq_of_lt_left v hlt
  rw [← e, ← Matrix.add_apply]
  exact h p.1 p.2

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_ratA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (G : GL (Fin n) E) (r s : Fin n) :
    adAt F P ((GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((G : Matrix (Fin n) (Fin n) E) r s) := by
  exact adAt_inclE F P _

theorem congE_of_near (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d d' : ℕ) (hd' : 1 ≤ d') (hdd : d' ≤ d)
    (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (G G' : GL (Fin n) E)
    (hG : ∀ w, (G : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (hG' : ∀ w, (G' : Matrix (Fin n) (Fin n) E) *ᵥ w = g' w)
    (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hy : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d : ℤ)))
    (hy' : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G' : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d' : ℤ))) :
    CongE P d' g' g := by
  set φ := adAt F P
  set y := x⁻¹ * GlobalTheory.TwU.ratA F G
  set y' := x⁻¹ * GlobalTheory.TwU.ratA F G'
  set H : GL (Fin n) E := G⁻¹ * G'
  have hyH : y * GlobalTheory.TwU.ratA F H = y' := by
    simp only [y, y', H, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set Y : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set Y' : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y' : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set R : Matrix (Fin n) (Fin n) (P.adicCompletion E) := ((GlobalTheory.TwU.ratA F H : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  have hYR : Y * R = Y' := by
    simp only [Y, Y', R, ← Matrix.map_mul, ← Units.val_mul, hyH]
  have hdA : ∀ r s, Valued.v ((Y - 1) r s) < 1 := fun r s => by
    refine lt_of_le_of_lt (hy r s) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hsum : ∀ r s, Valued.v (((R - 1) + (Y - 1) * (R - 1)) r s) ≤ WithZero.exp (-(d' : ℤ)) := fun r s => by
    have e : (R - 1) + (Y - 1) * (R - 1) = (Y' - 1) - (Y - 1) := by
      rw [← hYR]; noncomm_ring
    rw [e, Matrix.sub_apply]
    refine Valuation.map_sub_le _ (hy' r s) ((hy r s).trans ?_)
    rw [WithZero.exp_le_exp]; omega
  have hD := entries_le_of_add_mul Valued.v (Y - 1) (R - 1) _ hdA hsum

  have hH : ∀ r s, Valued.v (algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s)) ≤ WithZero.exp (-(d' : ℤ)) := by
    intro r s
    have e : (R - 1) r s = algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
      simp only [R, Matrix.map_apply, φ, adAt_ratA]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← e]; exact hD r s
  intro w hw
  have hHw : g ((H : Matrix (Fin n) (Fin n) E) *ᵥ w) = g' w := by
    rw [← hG, Matrix.mulVec_mulVec, ← Units.val_mul, ← hG']
    simp only [H, mul_inv_cancel_left]
  have e : (((qOf P : ℕ) : E) ^ d')⁻¹ • (g' w - g w) =
      g ((((qOf P : ℕ) : E) ^ d')⁻¹ • (((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w)) := by
    rw [map_smul, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hHw]
  rw [e]
  refine (hg _).2 ?_
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hw ⊢
  intro l
  have hs : Valued.v (algebraMap E (P.adicCompletion E) ((((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w) l)) ≤ WithZero.exp (-(d' : ℤ)) := by
    simp only [Matrix.mulVec, dotProduct, map_sum]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul, map_mul]
    calc _ ≤ WithZero.exp (-(d' : ℤ)) * 1 := mul_le_mul' (hH l k) (hw k)
      _ = _ := mul_one _
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast, hq]
  calc _ ≤ (WithZero.exp (-1 : ℤ) ^ d')⁻¹ * WithZero.exp (-(d' : ℤ)) := mul_le_mul_right hs _
    _ = 1 := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      simp

end Gen

end GlobalTheory.Mem.Col2.AdT.AdTieNear

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

set_option maxHeartbeats 800000 in

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  intro B X I hOk l Z a i fb dep dep' P κ g g' hg h1 hdd hF hF'
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hF hF'
  have hq := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) 0 P 1).2.1
  have hy := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep P) P _).2.2.1 hF
  have hy' := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep' P) P _).2.2.1 hF'
  exact congE_of_near (F := B.host.F) P.1 (dep P) (dep' P) h1 hdd _ g g'
    (GlobalTheory.TwU.seamGL (sm I l Z) g) (GlobalTheory.TwU.seamGL (sm I l Z) g')
    (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g w) (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g' w)
    hg hq hy hy'

end GlobalTheory.Mem.Col2.AdT.AdTieNear
