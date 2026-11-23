import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.LeviHC

section Alg

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def FinMod (K : Submodule ℂ M) (A : Subalgebra ℂ (Module.End ℂ M)) (v : M) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ A, y = K.mkQ (a v)})

def MonicFactorFinite : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (p q : ℂ → Module.End ℂ N),
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    ∀ v : N, FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range fun u => p u * q u), y = a v}) →
      FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range p), y = a v})

def RelativeCentre : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ B : Subalgebra ℂ A,
    (∀ b ∈ B, ∀ i j, X i j * b = b * X i j) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B, (∀ i j, X i j * z = z * X i j) →
      z ∈ Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA X)) ⊔ B

def MonicFactorFiniteMod : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K ∧ q u x ∈ K) →
    (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
    ∀ v ∈ M', FinMod K (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v

theorem coeff_mem_span {d : ℕ} {a : ℕ → M} {p : ℂ → M} (hp : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i)
    {i : ℕ} (hi : i < d + 1) : a i ∈ Submodule.span ℂ (Set.range p) := by
  set W := Submodule.span ℂ (Set.range p)
  have hdual : ∀ f : Module.Dual ℂ (M ⧸ W), f (W.mkQ (a i)) = 0 := by
    intro f
    let P : Polynomial ℂ :=
      ∑ j ∈ Finset.range (d + 1), Polynomial.C (f (W.mkQ (a j))) * Polynomial.X ^ j
    have hP : P = 0 := by
      apply Polynomial.funext
      intro u
      have h0 : W.mkQ (p u) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨u, rfl⟩)
      have h1 : f (W.mkQ (p u)) = ∑ j ∈ Finset.range (d + 1), u ^ j * f (W.mkQ (a j)) := by
        rw [hp u, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
      rw [h0, map_zero] at h1
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff i) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range.2 hi] using hc
  have hq : W.mkQ (a i) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 hdual
  exact (Submodule.Quotient.mk_eq_zero W).1 hq

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def SmG : Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | IsSm σ J f}
  add_mem' := isSm_add
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun a _ h => isSm_smul a h

theorem mem_SmG {f : GAd σ J → ℂ} : f ∈ SmG σ J ↔ IsSm σ J f := Iff.rfl

variable (σ J) in

def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z)

variable (σ J) in

def IsDer {w : InfinitePlace F} (τ : EmbOver E w)
    (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)) : Prop :=
  (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) ∧
    ∀ Z γ, IsLineOf σ J τ Z γ → ∀ f : SmG σ J, (D Z f).1 = lineDer γ f.1

variable {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}

theorem IsLineOf.skew (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 := by
  apply GlobalTheory.LineDerSum.skew_of_exp_unitary
  intro t
  obtain ⟨y, -, hy⟩ := hγ t
  rw [← hy, GlobalTheory.Orb.archMat_eq_archEquiv J h τ y]
  exact (archEquiv J h τ y).2

theorem IsLineOf.isRealLine (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, hγ.skew h, hγ⟩

theorem IsLineOf.unique (h : IsCMExt F E σ) {δ : ℝ → GAd σ J} (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ Z δ) :
    γ = δ := by
  funext t
  obtain ⟨y, hy1, hy2⟩ := hγ t
  obtain ⟨y', hy1', hy2'⟩ := hδ t
  have hyy : y = y' := by
    apply (archEquiv J h τ).injective
    apply Subtype.ext
    apply Units.ext
    rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h τ y, ← GlobalTheory.Orb.archMat_eq_archEquiv J h τ y', hy2, hy2']
  rw [hy1, hy1', hyy]

theorem IsLineOf.smul (hγ : IsLineOf σ J τ Z γ) (c : ℝ) : IsLineOf σ J τ (c • Z) fun t => γ (t * c) := by
  intro t
  obtain ⟨y, h1, h2⟩ := hγ (t * c)
  exact ⟨y, h1, by rw [h2, smul_smul]⟩

private theorem conjTranspose_map_eq_of_isHermND (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h.2.2.2 τ, hJ.1 i j]

private theorem isUnit_det_map_of_det_ne_zero {K : Type} [Field K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (hM : M.det ≠ 0) (τ : K →+* ℂ) : IsUnit (M.map τ).det := by
  have hd : (M.map τ).det = τ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 hM

theorem exists_isLineOf (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hZ : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0) :
    ∃ γ, IsLineOf σ J τ Z γ := by
  set A := J.map τ.1 with hAdef
  have hA : Aᴴ = A := conjTranspose_map_eq_of_isHermND h hJ τ.1
  have hd : IsUnit A.det := isUnit_det_map_of_det_ne_zero hJ.2 τ.1
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hd
  have hZ' : Zᴴ = -(A * Z * A⁻¹) := by
    have hz : Zᴴ * A = -(A * Z) := eq_neg_of_add_eq_zero_left hZ
    calc Zᴴ = Zᴴ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hd, Matrix.mul_one]
      _ = -(A * Z * A⁻¹) := by rw [hz, Matrix.neg_mul]
  have hunit : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A := by
    intro t
    have hconj : t • -(A * Z * A⁻¹) = A * (-(t • Z)) * A⁻¹ := by
      rw [Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    have hc : NormedSpace.exp (-(t • Z)) * NormedSpace.exp (t • Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • Z)).neg_left), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hZ', hconj,
      Matrix.exp_conj A _ hAu]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left A _ hd]
    rw [hc, Matrix.mul_one]
  have hmem : ∀ t : ℝ, (Matrix.isUnit_exp (t • Z)).unit ∈ Formalism.UG.UJ (starRingEnd ℂ) A :=
    fun t => hunit t
  refine ⟨fun t => embArch σ J w ((archEquiv J h τ).symm ⟨_, hmem t⟩), fun t => ⟨_, rfl, ?_⟩⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h τ, MulEquiv.apply_symm_apply]
  rfl

theorem conjTranspose_map (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := conjTranspose_map_eq_of_isHermND h hJ τ

omit [NumberField F] [NumberField E] in
theorem isUnit_det_map (hJ : IsHermND σ J) (τ : E →+* ℂ) : IsUnit (J.map τ).det := isUnit_det_map_of_det_ne_zero hJ.2 τ

def adj (A X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A⁻¹ * Xᴴ * A

theorem skew_parts {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hd : IsUnit A.det) (X : Matrix (Fin n) (Fin n) ℂ) :
    (((1 / 2 : ℂ) • (X - adj A X))ᴴ * A + A * ((1 / 2 : ℂ) • (X - adj A X)) = 0) ∧
    (((-Complex.I / 2 : ℂ) • (X + adj A X))ᴴ * A + A * ((-Complex.I / 2 : ℂ) • (X + adj A X)) = 0) ∧
    X = (1 / 2 : ℂ) • (X - adj A X) + Complex.I • ((-Complex.I / 2 : ℂ) • (X + adj A X)) := by
  have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hd
  have h2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hd
  have e1 : (adj A X)ᴴ * A = A * X := by
    simp only [adj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hA, Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : A * adj A X = Xᴴ * A := by
    simp only [adj, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have s2 : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
    rw [Complex.star_def, map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have s3 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul, e1,
      Matrix.mul_smul, Matrix.mul_sub, e2, s1]
    module
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul, e1,
      Matrix.mul_smul, Matrix.mul_add, e2, s2]
    have : (-Complex.I / 2 : ℂ) = -(Complex.I / 2) := by ring
    rw [this, neg_smul]
    module
  · rw [smul_smul, s3]
    module

theorem exists_lines (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ γ₁ γ₂, IsLineOf σ J τ ((1 / 2 : ℂ) • (X - adj (J.map τ.1) X)) γ₁ ∧
      IsLineOf σ J τ ((-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X)) γ₂ ∧
      X = (1 / 2 : ℂ) • (X - adj (J.map τ.1) X) + Complex.I • ((-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X)) := by
  obtain ⟨s1, s2, s3⟩ := skew_parts (conjTranspose_map h hJ τ.1) (isUnit_det_map hJ τ.1) X
  obtain ⟨γ₁, h1⟩ := exists_isLineOf (τ := τ) h hJ s1
  obtain ⟨γ₂, h2⟩ := exists_isLineOf (τ := τ) h hJ s2
  exact ⟨γ₁, γ₂, h1, h2, s3⟩

variable {n₁ : ℕ}

def frame (H : Plane E n n₁) : Matrix (Fin n) (Fin (1 + n₁ + 1)) E :=
  Matrix.of fun r => Fin.addCases (Fin.addCases (fun _ => H.x r) fun k => H.ι r k) fun _ => H.y r

def mid (k : Fin n₁) : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.natAdd 1 k)

def blk (n₁ : ℕ) : Fin (1 + n₁ + 1) → ℕ := Fin.addCases (Fin.addCases (fun _ => 0) fun _ => 1) fun _ => 2

omit [NumberField E] in
theorem frame_alt (H : Plane E n n₁) (r : Fin n) (a : Fin 1) : frame H r (Fin.castAdd 1 (Fin.castAdd n₁ a)) = H.x r := by simp [frame]

omit [NumberField E] in
theorem frame_mid (H : Plane E n n₁) (r : Fin n) (k : Fin n₁) : frame H r (mid k) = H.ι r k := by simp [frame, mid]

omit [NumberField E] in
theorem frame_y (H : Plane E n n₁) (r : Fin n) (a : Fin 1) : frame H r (Fin.natAdd (1 + n₁) a) = H.y r := by simp [frame]

theorem block_matrix_mulVec_basis (a : Fin 1) : blk n₁ (Fin.castAdd 1 (Fin.castAdd n₁ a)) = 0 := by simp [blk]

theorem blk_mid (k : Fin n₁) : blk n₁ (mid k) = 1 := by simp [blk, mid]

theorem blk_y (a : Fin 1) : blk n₁ (Fin.natAdd (1 + n₁) a) = 2 := by simp [blk]

end GlobalTheory.LeviHC

end
