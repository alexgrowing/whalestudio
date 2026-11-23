import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearOfGramEqStatement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.TenTypes

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset Finset.subset_union_left ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]

private theorem star_fockF_comm {σ : Type} (f g : MvPolynomial σ ℂ) :
    star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [fockF_eq_fockL g f, Formalism.L2.DIV.fockL_apply]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, star_mul', star_star, star_natCast]

theorem nfAll_add_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p p' q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (p + p') q = nfAll lam p q + nfAll lam p' q := by
  unfold nfAll
  rw [fockF_eq_fockL (p + p') q, map_add, ← fockF_eq_fockL p q, ← fockF_eq_fockL p' q, add_div]

theorem nfAll_smul_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (c : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (c • p) q = c * nfAll lam p q := by
  unfold nfAll
  rw [fockF_eq_fockL (c • p) q, map_smul, ← fockF_eq_fockL p q, smul_eq_mul, mul_div_assoc]

theorem nfAll_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam q p = star (nfAll lam p q) := by
  unfold nfAll
  rw [← starRingEnd_apply, map_div₀, map_prod]
  simp only [starRingEnd_apply, star_fockF_comm]

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have hX : MvPolynomial.eval (fun w : Fin n × Fin n => x w.1 w.2)
        (Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v)) = (g * x) v.1 v.2 := by
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
    simp only [map_mul, hp, hX, MvPolynomial.eval_X]

theorem factor_eq {n : ℕ} (m o a b : Matrix (Fin n) (Fin n) ℂ) (hm : m ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ho : IsUnit o.det) (s : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) (hab : a = o * m * o⁻¹ * b) :
    (o⁻¹ * a).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * a) v.1 v.2)
        ((m.det ^ (-s)) • Formalism.GradedWeylDivisibility.rowAct ℂ mᴴ p) =
      (o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p := by
  have hmm : mᴴ * m = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hm
    rwa [Matrix.star_eq_conjTranspose] at this
  have hdet : m.det ≠ 0 := by
    have := congrArg Matrix.det hmm
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have key : o⁻¹ * a = m * (o⁻¹ * b) := by
    rw [hab]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc o⁻¹ o, Matrix.nonsing_inv_mul o ho, Matrix.one_mul]
  rw [key, Matrix.det_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_rowAct mᴴ (m * (o⁻¹ * b)) p, ← Matrix.mul_assoc mᴴ m, hmm, Matrix.one_mul, mul_zpow, _root_.zpow_neg]
  have e : m.det ^ s * (m.det ^ s)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero s hdet)
  linear_combination
    ((o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p) * e

theorem tensor_dict : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  intro ι _ k n h lam u hu Vl _ _ πl hπ W _ _ tens htens hspan
  have hj := fun τ => GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module k n h (lam τ) (u τ) (hu τ) (Vl τ) (πl τ) (hπ τ)
  choose j hjmem hjonto hjnorm hjeq using hj
  obtain ⟨hten, hdef, hfn⟩ := GlobalTheory.T.normalizedFockForm_pureTensor_properties ι n lam
  obtain ⟨Jp, hJa, hJn⟩ := GlobalTheory.T.exists_conjLinear_of_gram_eq' W (MvPolynomial (ι × Fin n × Fin n) ℂ) (nfAll lam)
    (∀ τ, Vl τ) tens (fun x => ten fun τ => j τ (x τ)) (nfAll_add_left lam) (nfAll_smul_left lam)
    (nfAll_symm lam) hdef hspan (fun x x' => by
      show nfAll lam (ten fun τ => j τ (x' τ)) (ten fun τ => j τ (x τ)) = _
      rw [hten, htens]
      exact Finset.prod_congr rfl fun τ _ => hjnorm τ (x τ) (x' τ))
  have hall : ∀ ξ : W, ξ ∈ Submodule.span ℂ (Set.range tens) := fun ξ => by
    rw [hspan]; exact Submodule.mem_top
  refine ⟨Jp, ?_, ?_, hJn, ?_⟩
  · have hle : Submodule.span ℂ (Set.range tens) ≤ (CSpan lam).comap Jp := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show Jp (tens x) ∈ CSpan lam
      rw [hJa x]
      exact Submodule.subset_span ⟨fun τ => j τ (x τ), fun τ => hjmem τ (x τ), rfl⟩
    intro ξ
    exact hle (hall ξ)
  · intro p hp
    unfold CSpan at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨f, hf, rfl⟩ := hp
      choose x hx using fun τ => hjonto τ (f τ) (hf τ)
      refine ⟨tens x, ?_⟩
      rw [hJa x]
      show (ten fun τ => j τ (x τ)) = ten f
      congr 1
      funext τ
      exact hx τ
    | zero => exact ⟨0, map_zero Jp⟩
    | add p q _ _ hp hq =>
      obtain ⟨ξ, rfl⟩ := hp
      obtain ⟨η, rfl⟩ := hq
      exact ⟨ξ + η, map_add Jp ξ η⟩
    | smul c p _ hp =>
      obtain ⟨ξ, rfl⟩ := hp
      refine ⟨(starRingEnd ℂ c) • ξ, ?_⟩
      rw [map_smulₛₗ, starRingEnd_self_apply]
  · intro m hm A hA G o ho ξ y y' hy
    induction hall ξ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [hA x, hJa, hJa, hfn, hfn]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hjeq τ (m τ) (hm τ) (x τ)]
      exact factor_eq (m τ) (o τ) (y.1 τ) (y'.1 τ) (hm τ) (ho τ) (shiftOf lam τ) (j τ (x τ)) (hy τ)
    | zero => simp
    | add z w _ _ hz hw => simp only [map_add, Pi.add_apply, hz, hw]
    | smul c z _ hz => simp only [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, hz]

end GlobalTheory.TenTypes
