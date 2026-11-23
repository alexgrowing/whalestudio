import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_crd_of_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u hu
  obtain ⟨hC, b, hZ⟩ := (mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF u).1 hu
  set s := sigR (AF F) σ with hsdef
  set M := (matHom _ σ J u).1 with hMdef
  have hU : cT s M * adMat F J * M = adMat F J := u.2
  have hs : ∀ a : AF F ⊗[F] E, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hF.cm x)
  have cc : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (cT s X) = X :=
    fun X => Matrix.ext fun i k => hs _
  have cadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X + Y) = cT s X + cT s Y :=
    fun X Y => Matrix.ext fun i k => map_add s _ _
  have csub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X - Y) = cT s X - cT s Y :=
    fun X Y => Matrix.ext fun i k => map_sub s _ _
  have cad : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), cT s (adMat F X) = adMat F (cT (σ : E →+* E) X) :=
    fun X => GlobalTheory.AutFunCounterexample.cT_map_gen σ X
  have gram : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      cT s (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := fun X Y => by
    rw [cad]; simp only [adMat, Matrix.map_mul]
  have unit : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin b) (AF F ⊗[F] E)),
      cT s (M * X) * adMat F J * (M * Y) = cT s X * adMat F J * Y := fun X Y => by
    have e : cT s X * cT s M * adMat F J * (M * Y) = cT s X * (cT s M * adMat F J * M) * Y := by
      simp only [Matrix.mul_assoc]
    rw [Formalism.UG.cT_mul, e, hU]
  have ad0 : ∀ {a b : ℕ}, adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := fun {a b} => Matrix.map_zero _ (map_zero _)
  have ad1 : ∀ {a : ℕ}, adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun {a} => Matrix.map_one _ (map_zero _) (map_one _)

  have h1 : cT s (adMat F C) * adMat F J * (M * adMat F D) = 1 := by
    conv_lhs => rw [← hC]
    rw [unit, gram, hF.cd, ad1]
  have h2 : cT s (adMat F Z) * adMat F J * (M * adMat F D) = - cT s b := by
    have e := unit (adMat F Z) (adMat F D)
    rw [hZ, gram, hF.zd, ad0, cadd, Formalism.UG.cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (cT s b),
      Matrix.mul_assoc (cT s b), h1, Matrix.mul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  set c := cT s (adMat F D) * adMat F J * (M * adMat F D) with hc
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) +
      adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have e := congrArg (fun X => adMat F X) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
    simp only [cad, adMat]
    exact e
  have hD : M * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
    conv_lhs => rw [← Matrix.one_mul (M * adMat F D), ← hsum]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F Z)),
      ← Matrix.mul_assoc (cT s (adMat F C)), h1, h2, Matrix.mul_one, plus, Matrix.mul_neg, Matrix.mul_neg, ← hc]
    abel
  refine ⟨b, c, ⟨hC, hZ, hD⟩, ?_⟩

  have h0 := unit (adMat F D) (adMat F D)
  rw [gram, hF.dd, ad0] at h0
  have hP : cT s (plus σ J₀ b) = b * adMat F J₀⁻¹ := by
    rw [plus, Formalism.UG.cT_mul, cc, cad, GlobalTheory.UAut.cT_form_inv hF.herm₀]
  conv_lhs at h0 => rw [hD]
  rw [cadd, csub, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hP, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (cT s c),
    Matrix.mul_assoc (cT s c), ← hD, h1, h2, ← hc, Matrix.mul_one] at h0
  rw [← h0, plus, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.SphEis
