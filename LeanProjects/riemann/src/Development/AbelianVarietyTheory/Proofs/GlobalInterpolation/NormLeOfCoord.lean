import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds

noncomputable section

namespace GlobalTheory.LvT.PtNorm

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
open Formalism.REAL (fockF)
open Formalism.L2.DIV (fockL fockS)
open scoped ComplexOrder Matrix

theorem psd_had {κ : Type} {A B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i j => A i j * B i j).PosSemidef := hA.hadamard hB

theorem psd_prod {ι κ : Type} [Fintype κ] (A B : ι → Matrix κ κ ℂ) (hB : ∀ τ, (B τ).PosSemidef)
    (hAB : ∀ τ, (A τ - B τ).PosSemidef) (s : Finset ι) :
    (Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - (Matrix.of fun i j => ∏ τ ∈ s, B τ i j)).PosSemidef := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : κ => (1 : ℂ))
      convert h using 1
      ext i j
      simp [Matrix.vecMulVec]
    · simpa using Matrix.PosSemidef.zero
  | insert τ s hτ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · convert psd_had (hB τ) h1 using 1
      ext i j
      simp [Finset.prod_insert hτ]
    · have h3 := (psd_had (hAB τ) (h2.add h1)).add (psd_had (hB τ) h2)
      convert h3 using 1
      ext i j
      simp [Finset.prod_insert hτ]
      ring

theorem fockF_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = fockL g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) g f (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  rw [Formalism.L2.DIV.fockL_apply, h]

theorem fockL_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockL f f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [← fockF_eq]; exact (Formalism.L2.DIV.ps_fockF_pos f hf).le

def gram {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : Matrix κ κ ℂ := Matrix.of fun i j => fockL (v i) (v j)

theorem gram_dot {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (x : κ → ℂ) :
    star x ⬝ᵥ (gram v) *ᵥ x = fockL (∑ i, x i • v i) (∑ i, x i • v i) := by
  simp only [gram, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_herm {σ κ : Type} (v : κ → MvPolynomial σ ℂ) : (gram v).IsHermitian := by
  ext i j
  simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact (Formalism.L2.DIV.fockL_symm _ _).symm

theorem gram_psd {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) : (gram v).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_herm v) fun x => by rw [gram_dot]; exact fockL_nonneg _

theorem gram_sub_psd {σ σ' κ : Type} [Fintype κ] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (F : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ' ℂ) (C : ℝ)
    (h : ∀ f ∈ V, (fockL (F f) (F f)).re ≤ C * (fockL f f).re) (v : κ → MvPolynomial σ ℂ) (hv : ∀ i, v i ∈ V) :
    ((C : ℂ) • gram v - gram fun i => F (v i)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.sub ?_ (gram_herm _)
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (gram_herm v).eq]
    simp
  · rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, gram_dot, gram_dot]
    have e : ∑ i, x i • F (v i) = F (∑ i, x i • v i) := by simp
    rw [e]
    have hm : ∑ i, x i • v i ∈ V := V.sum_mem fun i _ => V.smul_mem _ (hv i)
    have h1 := h _ hm
    have h2 := (Complex.le_def.mp (fockL_nonneg (∑ i, x i • v i))).2
    have h3 := (Complex.le_def.mp (fockL_nonneg (F (∑ i, x i • v i)))).2
    refine Complex.le_def.mpr ⟨?_, ?_⟩
    · simp only [smul_eq_mul, Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul]; linarith
    · simp only [smul_eq_mul, Complex.zero_im, Complex.sub_im, Complex.im_ofReal_mul, ← h2, ← h3]; simp

def eN {n : ℕ} (l : DomWeight n) : ℝ := (fockF (extremal ℂ n l) (extremal ℂ n l)).re

theorem eN_pos {n : ℕ} (l : DomWeight n) : 0 < eN l :=
  (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).1

theorem eN_eq {n : ℕ} (l : DomWeight n) : fockF (extremal ℂ n l) (extremal ℂ n l) = (eN l : ℂ) := by
  have h := (Complex.lt_def.mp (Formalism.L2.DIV.ps_fockF_pos (extremal ℂ n l) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))).2
  exact Complex.ext (by simp [eN]) (by simpa using h.symm)

def sqL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g l.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}
  (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

def brT (X : Ch D u) (br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)) (τ : D.what₂.Tau) : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ :=
  ((sqrtT X ^ (-X.fm.deg τ) : ℂˣ) : ℂ) • br τ

end GlobalTheory.LvT.PtNorm
