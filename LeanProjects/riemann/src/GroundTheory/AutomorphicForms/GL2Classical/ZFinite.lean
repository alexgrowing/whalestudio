import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Complexify
import GroundTheory.AutomorphicForms.GL2Classical

open NumberField Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

def gl2WeightChar (k : ℤ) (B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (k : ℂ) / 2 * (B 0 0 + B 1 1) - k * (Complex.I * B 1 0 + B 1 1)

def gl2HolCoeff (B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  B 0 1 + B 1 0 + Complex.I * (B 0 0 - B 1 1)

def entryLiftKappa (k : ℤ) (F : ℂ → ℂ) (m : Fin 2 → Fin 2 → ℝ) : ℂ :=
  (Real.sqrt (m 0 0 * m 1 1 - m 0 1 * m 1 0) : ℂ) ^ k *
    (deriv F (((m 0 0 : ℂ) * Complex.I + m 0 1) * ((m 1 0 : ℂ) * Complex.I + m 1 1)⁻¹) *
        ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℝ) : ℂ) * ((m 1 0 : ℂ) * Complex.I + m 1 1)⁻¹ ^ 2 -
      k * F (((m 0 0 : ℂ) * Complex.I + m 0 1) * ((m 1 0 : ℂ) * Complex.I + m 1 1)⁻¹) * m 1 0 *
        ((m 1 0 : ℂ) * Complex.I + m 1 1)⁻¹) *
    ((m 1 0 : ℂ) * Complex.I + m 1 1) ^ (-k)

theorem hasDerivAt_entryLift_comp {k : ℤ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    {m : ℝ → Fin 2 → Fin 2 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hm : HasDerivAt m (fun i j => ∑ a, m 0 i a * A a j) 0)
    (hpos : 0 < m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0) :
    HasDerivAt (fun t => entryLift k F (m t))
      (gl2WeightChar k (A.map (↑)) * entryLift k F (m 0) +
        gl2HolCoeff (A.map (↑)) * entryLiftKappa k F (m 0)) 0 := by
  have hc : ∀ i j, HasDerivAt (fun t => m t i j) (m 0 i 0 * A 0 j + m 0 i 1 * A 1 j) 0 := fun i j => by
    simpa [Fin.sum_univ_two] using hasDerivAt_pi.1 (hasDerivAt_pi.1 hm i) j
  have hcC : ∀ i j, HasDerivAt (fun t => ((m t i j : ℝ) : ℂ))
      (((m 0 i 0 * A 0 j + m 0 i 1 * A 1 j : ℝ) : ℂ)) 0 := fun i j => (hc i j).ofReal_comp

  have hD : HasDerivAt (fun t => m t 0 0 * m t 1 1 - m t 0 1 * m t 1 0) _ 0 :=
    ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  have hS := (hD.sqrt hpos.ne').ofReal_comp
  have hS0 : (Real.sqrt (m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hSk := HasDerivAt.comp (h := fun t => ((Real.sqrt (m t 0 0 * m t 1 1 - m t 0 1 * m t 1 0) : ℝ) : ℂ))
    0 (hasDerivAt_zpow k _ (Or.inl hS0)) hS

  have hden : HasDerivAt (fun t => (m t 1 0 : ℂ) * Complex.I + m t 1 1) _ 0 :=
    ((hcC 1 0).mul_const Complex.I).add (hcC 1 1)
  have hnum : HasDerivAt (fun t => (m t 0 0 : ℂ) * Complex.I + m t 0 1) _ 0 :=
    ((hcC 0 0).mul_const Complex.I).add (hcC 0 1)
  have hden0 : ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    rw [h1, h2] at hpos
    simp at hpos
  have hinv := HasDerivAt.comp (h := fun t => (m t 1 0 : ℂ) * Complex.I + m t 1 1) 0
    (hasDerivAt_inv hden0) hden
  have hz : HasDerivAt (fun t => ((m t 0 0 : ℂ) * Complex.I + m t 0 1) * ((m t 1 0 : ℂ) * Complex.I + m t 1 1)⁻¹)
    _ 0 := hnum.mul hinv
  have hq : 0 < (((m 0 0 0 : ℂ) * Complex.I + m 0 0 1) * ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1)⁻¹).im := by
    rw [← div_eq_mul_inv, Complex.div_im]
    have hns : 0 < Complex.normSq ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1) := Complex.normSq_pos.2 hden0
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [← sub_div]
    apply div_pos _ hns
    nlinarith
  have hFd : HasDerivAt F (deriv F (((m 0 0 0 : ℂ) * Complex.I + m 0 0 1) *
      ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1)⁻¹)) (((m 0 0 0 : ℂ) * Complex.I + m 0 0 1) *
      ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1)⁻¹) :=
    (hF.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hq)).hasDerivAt
  have hFz := HasDerivAt.comp (h := fun t => ((m t 0 0 : ℂ) * Complex.I + m t 0 1) *
    ((m t 1 0 : ℂ) * Complex.I + m t 1 1)⁻¹) 0 hFd hz
  have hdk := HasDerivAt.comp (h := fun t => (m t 1 0 : ℂ) * Complex.I + m t 1 1) 0
    (hasDerivAt_zpow (-k) _ (Or.inl hden0)) hden
  have htot := (hSk.mul hFz).mul hdk
  refine htot.congr_deriv ?_

  simp only [Function.comp_apply, Pi.mul_apply, gl2WeightChar, gl2HolCoeff, entryLift, entryLiftKappa,
    Matrix.map_apply]
  rw [zpow_sub_one₀ hS0, zpow_sub_one₀ hden0]
  have hs2 : (Real.sqrt (m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0) : ℂ) *
      (Real.sqrt (m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0) : ℂ) =
      (m 0 0 0 : ℂ) * m 0 1 1 - m 0 0 1 * m 0 1 0 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
    push_cast
    ring
  push_cast
  generalize (Real.sqrt (m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0) : ℂ) = s at hs2 hS0 ⊢
  generalize F (((m 0 0 0 : ℂ) * Complex.I + m 0 0 1) * ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1)⁻¹) = X
  generalize deriv F (((m 0 0 0 : ℂ) * Complex.I + m 0 0 1) * ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1)⁻¹) = Y
  generalize ((m 0 1 0 : ℂ) * Complex.I + m 0 1 1) ^ (-k) = Q
  generalize s ^ k = P
  generalize (m 0 0 0 : ℂ) = p at hs2 hden0 ⊢
  generalize (m 0 0 1 : ℂ) = q at hs2 hden0 ⊢
  generalize (m 0 1 0 : ℂ) = r at hs2 hden0 ⊢
  generalize (m 0 1 1 : ℂ) = u at hs2 hden0 ⊢
  have hs2' : s ^ 2 = p * u - q * r := by rw [sq, hs2]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq, neg_one_mul]
  field_simp
  ring_nf
  simp only [Complex.I_sq, hI3, hs2']
  ring_nf

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem archSlice_adelicLift_expG {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (g : AdelicGL ℚ 2) (Y : archLie ℚ 2) :
    archSlice (adelicLift N k f) g (1 * (isExpLieAlgebra ℚ 2).expG Y) =
      entryLift k (f ∘ ofComplex) (fun i j =>
        ∑ a, (decompGL N g : Matrix (Fin 2) (Fin 2) ℝ) i a * archLin (NormedSpace.exp ((Y : ArchMatrix ℚ 2))) a j) := by
  obtain ⟨hpos, γ, u, hu, hg⟩ := decompGL_spec N g
  set h := decompGL N g
  have hPval : (fun i j => ∑ a, (h : Matrix (Fin 2) (Fin 2) ℝ) i a *
      archLin (NormedSpace.exp ((Y : ArchMatrix ℚ 2))) a j) =
      ((h * archToReal ((isExpLieAlgebra ℚ 2).expG Y) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext i j
    rw [Units.val_mul, Matrix.mul_apply]
    rfl
  have hdet : 0 < (h * archToReal ((isExpLieAlgebra ℚ 2).expG Y)).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hpos (det_archToReal_expG_pos Y)
  rw [archSlice_apply, one_mul]
  conv_lhs => rw [hg]
  rw [infEmb_eq_realEmb, mul_assoc _ _ (realEmb _), ← realEmb_mul_finEmb_comm, ← mul_assoc,
    mul_assoc (diagonal ℚ 2 γ), ← map_mul, adelicLift_apply hf γ hdet hu, archLift_eq_entryLift k f hdet, hPval]

theorem uAction_ι_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f)
    (X : (isExpLieAlgebra ℚ 2).lieSubalgebra) (g : AdelicGL ℚ 2) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ :
        AdelicGL ℚ 2 → ℂ) g =
      gl2WeightChar k ((lieRealMat X).map (↑)) * adelicLift N k f g +
        gl2HolCoeff ((lieRealMat X).map (↑)) * entryLiftKappa k (f ∘ ofComplex) (decompGL N g) := by
  rw [uAction_ι_apply]
  have hF : DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} := mdifferentiable_iff.1 hhol
  have h1 := (isExpLieAlgebra ℚ 2).hasDerivAt_rightDeriv (isArchSmooth_adelicLift hf hhol g)
    ((isExpLieAlgebra ℚ 2).ofLie X) 1
  obtain ⟨hpos, -⟩ := decompGL_spec N g
  set h := decompGL N g
  set m : ℝ → Fin 2 → Fin 2 → ℝ := fun t i j => ∑ a, (h : Matrix (Fin 2) (Fin 2) ℝ) i a *
    archLin (NormedSpace.exp (t • (X : ArchMatrix ℚ 2))) a j with hmdef
  have hlin1 : ∀ a j : Fin 2, archLin (1 : ArchMatrix ℚ 2) a j = (1 : Matrix (Fin 2) (Fin 2) ℝ) a j := by
    intro a j
    rw [← archRealEquiv_apply, map_one]
  have hm0 : m 0 = fun i j => (h : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    funext i j
    simp only [hmdef, zero_smul, NormedSpace.exp_zero, hlin1]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  have hexp : HasDerivAt (fun t : ℝ => archLin (NormedSpace.exp (t • (X : ArchMatrix ℚ 2))))
      (archLin (X : ArchMatrix ℚ 2)) 0 := by
    have := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X : ArchMatrix ℚ 2) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, mul_one] at this
    exact archLin.hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
  have hm : HasDerivAt m (fun i j => ∑ a, m 0 i a * lieRealMat X a j) 0 := by
    rw [hm0]
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    refine HasDerivAt.fun_sum fun a _ => ?_
    exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hexp a) j).const_mul _
  have hpos' : 0 < m 0 0 0 * m 0 1 1 - m 0 0 1 * m 0 1 0 := by
    rw [hm0]
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hpos
    exact hpos
  have h2 := hasDerivAt_entryLift_comp (k := k) hF hm hpos'
  have hfun : (fun t : ℝ => archSlice (adelicLift N k f) g
      (1 * (isExpLieAlgebra ℚ 2).expG (t • (isExpLieAlgebra ℚ 2).ofLie X))) =
      fun t => entryLift k (f ∘ ofComplex) (m t) := by
    funext t
    rw [archSlice_adelicLift_expG hf g]
    rfl
  rw [hfun] at h1
  have hE : entryLift k (f ∘ ofComplex) (m 0) = adelicLift N k f g := by
    have := archSlice_adelicLift_expG (N := N) hf g 0
    rw [(isExpLieAlgebra ℚ 2).expG_zero, one_mul, archSlice_apply, map_one, mul_one] at this
    rw [this]
    congr 1
    rw [hm0]
    funext i j
    simp only [ZeroMemClass.coe_zero, NormedSpace.exp_zero, hlin1]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  rw [h1.unique h2, hE, hm0]

theorem gl2ArchRep_ι_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f)
    (B : HarishChandra.gl 2) (g : AdelicGL ℚ 2) :
    (gl2ArchRep (UniversalEnvelopingAlgebra.ι ℂ B) ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ :
        AdelicGL ℚ 2 → ℂ) g =
      gl2WeightChar k B * adelicLift N k f g +
        gl2HolCoeff B * entryLiftKappa k (f ∘ ofComplex) (decompGL N g) := by
  rw [gl2ArchRep_ι, complexOpGL2, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
    Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, realOpGL2, realOpGL2,
    uAction_ι_adelicLift hf hhol, uAction_ι_adelicLift hf hhol, lieRealMat_lieOfRealMat,
    lieRealMat_lieOfRealMat]
  conv_rhs => rw [← map_ofReal_reMat_add_imMat B]
  simp only [gl2WeightChar, gl2HolCoeff, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

theorem gl2ArchRep_ι_adelicLift_of_holCoeff {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f)
    {B : HarishChandra.gl 2} (hB : gl2HolCoeff B = 0) :
    gl2ArchRep (UniversalEnvelopingAlgebra.ι ℂ B) ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ =
      gl2WeightChar k B • ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ := by
  apply Subtype.ext
  funext g
  rw [gl2ArchRep_ι_adelicLift hf hhol, hB, zero_mul, add_zero]
  rfl

def cayleyGL2 : (HarishChandra.gl 2)ˣ where
  val := !![1, 0; -Complex.I, 1]
  inv := !![1, 0; Complex.I, 1]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp

theorem cayleyGL2_conj (a : Fin 2 × Fin 2) :
    (cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E a * ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2) =
      !![1, 0; -Complex.I, 1] * Matrix.single a.1 a.2 1 * !![1, 0; Complex.I, 1] := rfl

theorem cayleyGL2_conj_zero_zero :
    (cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E (0, 0) *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2) = !![1, 0; -Complex.I, 0] := by
  rw [cayleyGL2_conj, show Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) = !![1, 0; 0, 0] by
    ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem cayleyGL2_conj_zero_one :
    (cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E (0, 1) *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2) = !![Complex.I, 1; 1, -Complex.I] := by
  rw [cayleyGL2_conj, show Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) = !![0, 1; 0, 0] by
    ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem cayleyGL2_conj_one_one :
    (cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E (1, 1) *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2) = !![0, 0; Complex.I, 1] := by
  rw [cayleyGL2_conj, show Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = !![0, 0; 0, 1] by
    ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem gl2HolCoeff_cayleyGL2_conj : ∀ a : Fin 2 × Fin 2, a.1 ≤ a.2 →
    gl2HolCoeff ((cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E a *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2)) = 0 := by
  simp only [Prod.forall, Fin.forall_fin_two]
  refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, fun h => absurd h (by decide), fun _ => ?_⟩
  · rw [cayleyGL2_conj_zero_zero]
    simp [gl2HolCoeff]
  · rw [cayleyGL2_conj_zero_one]
    simp [gl2HolCoeff]
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [cayleyGL2_conj_one_one]
    simp [gl2HolCoeff]

theorem gl2WeightChar_cayleyGL2_conj_zero_one :
    gl2WeightChar k ((cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E (0, 1) *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2)) = 0 := by
  rw [cayleyGL2_conj_zero_one]
  simp [gl2WeightChar]

theorem gl2WeightChar_cayleyGL2_conj_diag : ∀ i : Fin 2,
    gl2WeightChar k ((cayleyGL2 : HarishChandra.gl 2) * HarishChandra.E (i, i) *
      ((cayleyGL2⁻¹ : (HarishChandra.gl 2)ˣ) : HarishChandra.gl 2)) = ![-(k : ℂ) / 2, (k : ℂ) / 2] i := by
  simp only [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [cayleyGL2_conj_zero_zero]
    simp [gl2WeightChar]
    ring_nf
  · rw [cayleyGL2_conj_one_one]
    simp [gl2WeightChar]

theorem gl2ArchRep_conj_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f) :
    (∀ a, HarishChandra.IsUpper a → gl2ArchRep (HarishChandra.conjU cayleyGL2 (HarishChandra.e a))
        ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ = 0) ∧
      ∀ i, gl2ArchRep (HarishChandra.conjU cayleyGL2 (HarishChandra.e (i, i)))
        ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ =
          ![-(k : ℂ) / 2, (k : ℂ) / 2] i • ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ := by
  refine ⟨fun a ha => ?_, fun i => ?_⟩
  · obtain ⟨i, j⟩ := a
    have hij : (i, j) = ((0 : Fin 2), (1 : Fin 2)) := by
      simp only [HarishChandra.IsUpper] at ha
      fin_cases i <;> fin_cases j <;> simp_all
    rw [hij, HarishChandra.e, HarishChandra.conjU_ι,
      gl2ArchRep_ι_adelicLift_of_holCoeff hf hhol (gl2HolCoeff_cayleyGL2_conj _ (by decide)),
      gl2WeightChar_cayleyGL2_conj_zero_one, zero_smul]
  · rw [HarishChandra.e, HarishChandra.conjU_ι,
      gl2ArchRep_ι_adelicLift_of_holCoeff hf hhol (gl2HolCoeff_cayleyGL2_conj _ le_rfl),
      gl2WeightChar_cayleyGL2_conj_diag]

theorem gl2ArchRep_ι_one_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f) :
    gl2ArchRep (UniversalEnvelopingAlgebra.ι ℂ (1 : HarishChandra.gl 2))
      ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ = 0 := by
  rw [gl2ArchRep_ι_adelicLift_of_holCoeff hf hhol (by simp [gl2HolCoeff])]
  have : gl2WeightChar k (1 : HarishChandra.gl 2) = 0 := by
    simp [gl2WeightChar]
    ring
  rw [this, zero_smul]

theorem isZFinite_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) (hhol : MDiff f) :
    IsZFinite (⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ : archSmooth ℚ 2) :=
  isZFinite_of_gl2ArchRep_conj cayleyGL2 _ (gl2ArchRep_conj_adelicLift hf hhol).1
    (gl2ArchRep_conj_adelicLift hf hhol).2

theorem isZFinite_liftEquiv_of_mdifferentiable (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hhol : MDiff (f : ℍ → ℂ)) :
    IsZFinite (⟨(liftEquiv N k f : AdelicGL ℚ 2 → ℂ), (liftEquiv_spec_of_mdifferentiable f hhol).2.1.1⟩ :
      archSmooth ℚ 2) := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  have e : (⟨(liftEquiv N k f : AdelicGL ℚ 2 → ℂ), (liftEquiv_spec_of_mdifferentiable f hhol).2.1.1⟩ :
      archSmooth ℚ 2) = ⟨adelicLift N k f, isArchSmooth_adelicLift hf hhol⟩ :=
    Subtype.ext (liftEquiv_apply f)
  rw [e]
  exact isZFinite_adelicLift hf hhol

theorem liftEquiv_mem_cuspForms (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∈ cuspForms ℚ 2 :=
  mem_cuspForms_of_isZFinite f (isZFinite_liftEquiv_of_mdifferentiable f.toSlashInvariantForm f.holo')

end GL2Classical

end

end GroundTheory.Automorphic
