import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

private theorem darb_skew {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {B : V → V → R} {κ : Type}
    [Fintype κ] (d : Darboux B κ) (a b : V) : B a b = -B b a := by
  rw [d.form, d.form]; ring

private theorem darb_nondeg {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {B : V → V → R} {κ : Type}
    [Fintype κ] (d : Darboux B κ) (a : V) (h : ∀ b, B a b = 0) : a = 0 := by
  classical
  apply d.e.injective
  rw [map_zero]
  ext i
  · have := h (d.e.symm (0, Pi.single i 1))
    rw [d.form, LinearEquiv.apply_symm_apply] at this
    simpa using this
  · have := h (d.e.symm (Pi.single i 1, 0))
    rw [d.form, LinearEquiv.apply_symm_apply] at this
    simpa using this

private theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

private theorem form_sum {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) : form σ J v w = ∑ i, ∑ k, v i * J i k * σ (w k) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem form_smul_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b : E) (v w : Fin n → E) :
    form σ J (a • v) (b • w) = a * σ b * form σ J v w := by
  simp only [form_sum, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem symp_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (p p' : Fin n → E) (q q' : Fin d → E) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB) (Matrix.vecMulVec (incV F p) (incV F q))
      (Matrix.vecMulVec (incV F p') (incV F q')) =
      -algebraMap F (AF F) (Algebra.trace F E (form σ JA p p' * form σ JB q q')) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have h : hTens (cA σ) (incM F JA) (incM F JB) (Matrix.vecMulVec (incV F p) (incV F q))
      (Matrix.vecMulVec (incV F p') (incV F q')) = inclR (F := F) (AF F) (form σ JA p p' * form σ JB q q') := by
    unfold hTens
    rw [form_sum, form_sum]
    simp_rw [Finset.sum_mul_sum]
    simp only [Matrix.vecMulVec_apply, map_mul, map_sum, incV, incM, Matrix.map_apply, hc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [symp, h, neg_one_mul, map_neg]
  exact congrArg Neg.neg (trace_one_tmul (AF F) _)

private theorem symp_rad {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (p : Fin n → E) (q : Fin d → E) (hq : q ᵥ* JB = 0) (B : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB) (Matrix.vecMulVec (incV F p) (incV F q)) B = 0 := by
  have h0 : ∀ l, ∑ j, incV F q j * incM F JB j l = 0 := fun l => by
    have := congrArg (inclR (F := F) (AF F)) (congrFun hq l)
    simpa only [Matrix.vecMul, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero, incV, incM, Matrix.map_apply]
      using this
  have h : hTens (cA σ) (incM F JA) (incM F JB) (Matrix.vecMulVec (incV F p) (incV F q)) B = 0 := by
    unfold hTens
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    calc _ = (incV F p i * incM F JA i k * cA σ (B k l)) * ∑ j, incV F q j * incM F JB j l := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.vecMulVec_apply]; ring
      _ = 0 := by rw [h0, mul_zero]
  rw [symp, h, mul_zero, map_zero]

theorem UpperTheory.skew_form_hermitian_twist :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (x y : Fin n → E) (x' y' : Fin d → E),
        form σ X.J x y = 1 → form σ W.J x' y' = 1 →
        (∀ a, σ (σ a) = a) ∧ W.J.det ≠ 0 ∧ ∃ l : E, l * σ l = 1 ∧ ∀ w w', form σ W.J w w' = l * σ (form σ W.J w' w) := by
  intro F E _ _ _ _ _ σ n d X W M x y x' y' hxy hxy'
  have key : ∀ p p' q q', Algebra.trace F E (form σ X.J p p' * form σ W.J q q') =
      -Algebra.trace F E (form σ X.J p' p * form σ W.J q' q) := fun p p' q q' => by
    have h := darb_skew M.co (Matrix.vecMulVec (incV F p) (incV F q)) (Matrix.vecMulVec (incV F p') (incV F q'))
    rw [symp_rat, symp_rat, neg_inj, ← map_neg] at h
    exact AdeleRing.algebraMap_injective (𝓞 F) F h
  have hbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  have htr : ∀ a, Algebra.trace F E (σ a) = Algebra.trace F E a := fun a =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hbij) a
  have hnd : ∀ a : E, (∀ b, Algebra.trace F E (a * b) = 0) → a = 0 := fun a h =>
    (traceForm_nondegenerate F E).1 a h
  have h1 : ∀ c : E, c + form σ X.J y x * form σ W.J y' x' * σ (σ c) = 0 := fun c => hnd _ fun b => by
    have h := key (σ c • x) (b • y) x' y'
    rw [form_smul_smul, form_smul_smul, hxy, hxy', mul_one, mul_one, ← map_mul, htr] at h
    rw [add_mul, map_add, h, neg_add_eq_zero]
    congr 1; ring
  have hk : form σ X.J y x * form σ W.J y' x' = -1 := by
    have := h1 1
    rw [map_one, map_one] at this
    linear_combination this
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    have := h1 a
    rw [hk] at this
    linear_combination -this
  have hl : ∀ w w', form σ W.J w w' = -σ (form σ X.J y x) * σ (form σ W.J w' w) := fun w w' => by
    have : form σ W.J w w' + σ (form σ X.J y x) * σ (form σ W.J w' w) = 0 := hnd _ fun a => by
      have h := key (a • x) ((1 : E) • y) w w'
      rw [form_smul_smul, form_smul_smul, hxy, map_one, mul_one, mul_one, one_mul,
        ← htr (σ a * _ * _), map_mul σ, map_mul σ, hσ] at h
      rw [add_mul, map_add, mul_comm, h, neg_add_eq_zero]
      congr 1; ring
    linear_combination this
  refine ⟨hσ, fun hdet => ?_, -σ (form σ X.J y x), ?_, hl⟩
  · obtain ⟨w, hw, hw0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have hz := darb_nondeg M.co _ (symp_rad σ X.J W.J x w hw0)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
    have hx : x = 0 := funext fun i => by
      have h : inclR (F := F) (AF F) (x i * w j) = inclR (F := F) (AF F) 0 := by
        rw [map_mul, map_zero]; exact congrFun (congrFun hz i) j
      exact (mul_eq_zero.mp (hinj h)).resolve_right hj
    rw [hx, form_sum] at hxy
    simp at hxy
  · have a := hl x' y'
    have b := hl y' x'
    rw [hxy', map_one, mul_one] at b
    rw [hxy', b] at a
    exact a.symm
