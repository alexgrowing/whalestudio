import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.KStabLie

variable {p q n : ℕ}

theorem Jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem isKC_iff (X : Mat p q) : IsKC X ↔ X * Jm p q = Jm p q * X := by
  rw [Jm_eq]
  constructor
  · intro h
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases a with a | a <;> rcases b with b | b
    · simp
    · simp [h (.inl a) (.inr b) (by simp [sameBlock])]
    · simp [h (.inr a) (.inl b) (by simp [sameBlock])]
    · simp
  · intro h a b hab
    have := congrFun (congrFun h a) b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rcases a with a | a <;> rcases b with b | b
    · simp [sameBlock] at hab
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (-1 / 2 : ℂ) * this
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (1 / 2 : ℂ) * this
    · simp [sameBlock] at hab

theorem Jm_sq (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases a <;> simp

theorem Jm_ct (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  cases a <;> simp

theorem mem_Kset {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {x : T.G}
    (hx : x ∈ T.Kset) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.REAL.Kset ε := by
  have h1 : Formalism.REAL.inUJ ε _ := h.cov_mem T x
  have h2 := (isKC_iff _).1 hx
  have h3 : Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := by
    rw [← h.reindex_Jm]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, h2]
  refine ⟨?_, h3⟩
  generalize Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g at h1 h3
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold Formalism.REAL.inUJ at h1
  rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc] at h1
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h1
  simpa only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] using h4

theorem smul_mem_upq {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  change (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h, smul_zero]

theorem expt_mem (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) (hK : IsKC X) (t : ℝ) :
    T.expt (t • X) ∈ T.Kset := by
  change IsKC _
  rw [T.expt_cov _ (smul_mem_upq hX t), isKC_iff]
  have h : Commute (t • X) (Jm p q) := Commute.smul_left ((isKC_iff X).1 hK) t
  exact h.exp_left.eq

theorem deriv_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] {f : ℝ → H} {y : H} (hf : HasDerivAt f y 0) (hS : ∀ t, f t ∈ S) : y ∈ S := by
  have hc : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hf) (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

theorem exists_decomp {Z : Mat p q} (hZ : IsKC Z) :
    ∃ X Y : Mat p q, X ∈ upq p q ∧ IsKC X ∧ Y ∈ upq p q ∧ IsKC Y ∧ Z = X + Complex.I • Y := by
  have hc : IsKC Zᴴ := by
    intro a b hab
    rw [Matrix.conjTranspose_apply, hZ b a (by cases a <;> cases b <;> simp_all [sameBlock]), star_zero]
  have h1 := (isKC_iff _).1 hZ
  have h2 := (isKC_iff _).1 hc
  refine ⟨(1 / 2 : ℂ) • (Z - Zᴴ), (-Complex.I / 2) • (Z + Zᴴ), ?_, ?_, ?_, ?_, ?_⟩
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.sub_apply, hZ a b hab, hc a b hab, sub_zero, smul_zero]
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    module
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.add_apply, hZ a b hab, hc a b hab, add_zero, smul_zero]
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
    module

theorem kstable_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  intro p q n e ε T R σ h hσ
  refine ⟨fun S hS hK v hv => ?_, fun W hW hK => ?_⟩
  · have : KFin T R.U.π v := by
      unfold KFin
      refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      change R.U.π k v ∈ S
      rw [hσ]
      exact hK _ (mem_Kset h T k.2) v hv
    exact (R.ι_range v).2 this
  · have key : ∀ X ∈ upq p q, IsKC X → ∀ w ∈ W, R.HK.act X w ∈ W := by
      intro X hX hXK w hw
      have : R.ι (R.HK.act X w) ∈ W.map R.ι := by
        refine deriv_mem _ (R.der X hX w) fun t => ?_
        rw [hσ]
        exact hK _ (mem_Kset h T (expt_mem T hX hXK t)) _ (Submodule.mem_map_of_mem hw)
      obtain ⟨u, hu, hu'⟩ := this
      rw [← R.ι_inj hu']
      exact hu
    intro Z hZ w hw
    obtain ⟨X, Y, hX, hXK, hY, hYK, rfl⟩ := exists_decomp hZ
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact W.add_mem (key X hX hXK w hw) (W.smul_mem _ (key Y hY hYK w hw))

end GlobalTheory.RealPar.KStabLie

end
