import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianBlockDecompositionHyperbolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairSplittingMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinatesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdaptedDarboux

section Glue

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n₁ d : ℕ}

def comb (f : Fin n₁ × Fin d → R) (g : Fin 2 × Fin d → R) : Fin (n₁ + 2) × Fin d → R :=
  fun k => Fin.addCases (motive := fun _ => R) (fun i => f (i, k.2)) (fun t => g (t, k.2)) k.1

@[simp] theorem comb_castAdd (f : Fin n₁ × Fin d → R) (g : Fin 2 × Fin d → R) (i : Fin n₁) (l : Fin d) :
    comb f g (Fin.castAdd 2 i, l) = f (i, l) := by simp [comb]

@[simp] theorem comb_natAdd (f : Fin n₁ × Fin d → R) (g : Fin 2 × Fin d → R) (t : Fin 2) (l : Fin d) :
    comb f g (Fin.natAdd n₁ t, l) = g (t, l) := by simp [comb]

theorem comb_ext {u v : Fin (n₁ + 2) × Fin d → R} (h1 : ∀ i l, u (Fin.castAdd 2 i, l) = v (Fin.castAdd 2 i, l))
    (h2 : ∀ t l, u (Fin.natAdd n₁ t, l) = v (Fin.natAdd n₁ t, l)) : u = v := by
  funext k
  rcases k with ⟨i, l⟩
  refine Fin.addCases (fun i => ?_) (fun t => ?_) i
  · exact h1 i l
  · exact h2 t l

theorem dot_comb (f f' : Fin n₁ × Fin d → R) (g g' : Fin 2 × Fin d → R) :
    comb f g ⬝ᵥ comb f' g' = f ⬝ᵥ f' + g ⬝ᵥ g' := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_add, comb_castAdd, comb_natAdd]

def top (z : Matrix (Fin (n₁ + 2)) (Fin d) A) : Matrix (Fin n₁) (Fin d) A := Matrix.of fun i l => z (Fin.castAdd 2 i) l

def glue (e₁ : Matrix (Fin n₁) (Fin d) A ≃ₗ[R] (Fin n₁ × Fin d → R) × (Fin n₁ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) :
    Matrix (Fin (n₁ + 2)) (Fin d) A ≃ₗ[R] (Fin (n₁ + 2) × Fin d → R) × (Fin (n₁ + 2) × Fin d → R) where
  toFun z := (comb (e₁ (top z)).1 (q (z (Fin.natAdd n₁ 1))), comb (e₁ (top z)).2 (p (z (Fin.natAdd n₁ 0))))
  invFun uv := Matrix.of fun r l => Fin.addCases (motive := fun _ => A)
    (fun i => e₁.symm (fun k => uv.1 (Fin.castAdd 2 k.1, k.2), fun k => uv.2 (Fin.castAdd 2 k.1, k.2)) i l)
    (fun t => ![p.symm (fun k => uv.2 (Fin.natAdd n₁ k.1, k.2)) l, q.symm (fun k => uv.1 (Fin.natAdd n₁ k.1, k.2)) l] t) r
  map_add' z z' := by
    have ht : top (z + z') = top z + top z' := rfl
    have hr : ∀ r, (z + z') r = z r + z' r := fun _ => rfl
    rw [ht]
    ext k <;> rcases k with ⟨i, l⟩ <;> refine Fin.addCases (fun i => ?_) (fun t => ?_) i <;> simp [comb, hr]
  map_smul' a z := by
    have ht : top (a • z) = a • top z := rfl
    have hr : ∀ r, (a • z) r = a • z r := fun _ => rfl
    rw [ht]
    ext k <;> rcases k with ⟨i, l⟩ <;> refine Fin.addCases (fun i => ?_) (fun t => ?_) i <;> simp [comb, hr]
  left_inv z := by
    ext r l
    refine Fin.addCases (fun i => ?_) (fun t => ?_) r
    · simp only [Matrix.of_apply, Fin.addCases_left, comb_castAdd]
      rw [show ((fun k : Fin n₁ × Fin d => (e₁ (top z)).1 (k.1, k.2)), fun k : Fin n₁ × Fin d => (e₁ (top z)).2 (k.1, k.2))
        = e₁ (top z) from rfl, LinearEquiv.symm_apply_apply]
      rfl
    · fin_cases t <;> simp [comb]
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    have ht : top ((Matrix.of fun r l => Fin.addCases (motive := fun _ => A)
        (fun i => e₁.symm (fun k => u (Fin.castAdd 2 k.1, k.2), fun k => v (Fin.castAdd 2 k.1, k.2)) i l)
        (fun t => ![p.symm (fun k => v (Fin.natAdd n₁ k.1, k.2)) l, q.symm (fun k => u (Fin.natAdd n₁ k.1, k.2)) l] t) r)) =
        e₁.symm (fun k => u (Fin.castAdd 2 k.1, k.2), fun k => v (Fin.castAdd 2 k.1, k.2)) := by
      ext i l; simp [top]
    have h0 : (Matrix.of fun r l => Fin.addCases (motive := fun _ => A)
        (fun i => e₁.symm (fun k => u (Fin.castAdd 2 k.1, k.2), fun k => v (Fin.castAdd 2 k.1, k.2)) i l)
        (fun t => ![p.symm (fun k => v (Fin.natAdd n₁ k.1, k.2)) l, q.symm (fun k => u (Fin.natAdd n₁ k.1, k.2)) l] t) r)
        (Fin.natAdd n₁ 0) = p.symm (fun k => v (Fin.natAdd n₁ k.1, k.2)) := by
      funext l; simp
    have h1 : (Matrix.of fun r l => Fin.addCases (motive := fun _ => A)
        (fun i => e₁.symm (fun k => u (Fin.castAdd 2 k.1, k.2), fun k => v (Fin.castAdd 2 k.1, k.2)) i l)
        (fun t => ![p.symm (fun k => v (Fin.natAdd n₁ k.1, k.2)) l, q.symm (fun k => u (Fin.natAdd n₁ k.1, k.2)) l] t) r)
        (Fin.natAdd n₁ 1) = q.symm (fun k => u (Fin.natAdd n₁ k.1, k.2)) := by
      funext l; simp
    show (comb _ _, comb _ _) = _
    beta_reduce
    rw [ht, h0, h1, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    ext k <;> rcases k with ⟨i, l⟩ <;> refine Fin.addCases (fun i => ?_) (fun t => ?_) i <;> simp

theorem glue_apply (e₁ : Matrix (Fin n₁) (Fin d) A ≃ₗ[R] (Fin n₁ × Fin d → R) × (Fin n₁ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) (z : Matrix (Fin (n₁ + 2)) (Fin d) A) :
    glue e₁ p q z = (comb (e₁ (top z)).1 (q (z (Fin.natAdd n₁ 1))), comb (e₁ (top z)).2 (p (z (Fin.natAdd n₁ 0)))) := rfl

end Glue

section Glue2

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n₁ d : ℕ}

theorem glue_form (e₁ : Matrix (Fin n₁) (Fin d) A ≃ₗ[R] (Fin n₁ × Fin d → R) × (Fin n₁ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) (B₁ : Matrix (Fin n₁) (Fin d) A → Matrix (Fin n₁) (Fin d) A → R)
    (h₁ : ∀ z z', B₁ z z' = (e₁ z).1 ⬝ᵥ (e₁ z').2 - (e₁ z').1 ⬝ᵥ (e₁ z).2) (z z' : Matrix (Fin (n₁ + 2)) (Fin d) A) :
    (glue e₁ p q z).1 ⬝ᵥ (glue e₁ p q z').2 - (glue e₁ p q z').1 ⬝ᵥ (glue e₁ p q z).2 =
      B₁ (top z) (top z') + (q (z (Fin.natAdd n₁ 1)) ⬝ᵥ p (z' (Fin.natAdd n₁ 0)) -
        q (z' (Fin.natAdd n₁ 1)) ⬝ᵥ p (z (Fin.natAdd n₁ 0))) := by
  simp only [glue_apply, dot_comb, h₁]
  ring

def mulLeft {m : ℕ} (Q P : Matrix (Fin m) (Fin m) A) (h1 : P * Q = 1) (h2 : Q * P = 1) :
    Matrix (Fin m) (Fin d) A ≃ₗ[R] Matrix (Fin m) (Fin d) A where
  toFun w := Q * w
  invFun z := P * z
  map_add' := Matrix.mul_add Q
  map_smul' a w := Matrix.mul_smul Q a w
  left_inv w := by
    show P * (Q * w) = w
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  right_inv z := by
    show Q * (P * z) = z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end Glue2

section Emb

variable {A : Type} [CommRing A] {n₁ d : ℕ}

def emb (z₀ : Matrix (Fin n₁) (Fin d) A) (a b : Fin d → A) : Matrix (Fin (n₁ + 2)) (Fin d) A :=
  Matrix.of fun r l => Fin.addCases (motive := fun _ => A) (fun i => z₀ i l) (fun t => ![a l, b l] t) r

@[simp] theorem top_emb (z₀ : Matrix (Fin n₁) (Fin d) A) (a b : Fin d → A) : top (emb z₀ a b) = z₀ := by
  ext i l; simp [top, emb]

@[simp] theorem emb_zero (z₀ : Matrix (Fin n₁) (Fin d) A) (a b : Fin d → A) : emb z₀ a b (Fin.natAdd n₁ 0) = a := by
  funext l; simp [emb]

@[simp] theorem emb_one (z₀ : Matrix (Fin n₁) (Fin d) A) (a b : Fin d → A) : emb z₀ a b (Fin.natAdd n₁ 1) = b := by
  funext l; simp [emb]

end Emb

theorem adapted_darboux : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∃ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
        Function.Injective j ∧
        (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
        (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH hM₁
  obtain rfl : n = n₁ + 2 := hH.rank
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX₁' : X₁.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX₁.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X₁.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_extension_symplectic_coordinates σ d W.J hσ hB.cm.2.2.1 hW.skew hW'
  let P : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E := Matrix.of fun r c =>
    Fin.addCases (motive := fun _ => E) (fun i => H.ι r i) (fun t => ![H.x r, H.y r] t) c
  have hPι : ∀ r i, P r (Fin.castAdd 2 i) = H.ι r i := fun r i => by simp [P]
  have hPx : ∀ r, P r (Fin.natAdd n₁ 0) = H.x r := fun r => by simp [P]
  have hPy : ∀ r, P r (Fin.natAdd n₁ 1) = H.y r := fun r => by simp [P]
  obtain ⟨hPdet, hG1, hG2, hG3, hG00, hG11, hG01, hG10⟩ :=
    GlobalTheory.T.hyperbolic_pair_splitting_matrix σ n₁ X.J X₁.J H.x H.y H.ι P hσ hX.herm hX₁' hH.xx hH.yy hH.xy hH.orth hH.gram hPι hPx hPy
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (Ne.isUnit hPdet)
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (Ne.isUnit hPdet)
  have hinc : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have hinc1 : incM F (1 : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : incM F P * incM F P⁻¹ = 1 := by rw [← hinc, hPQ, hinc1]
  have h2 : incM F P⁻¹ * incM F P = 1 := by rw [← hinc, hQP, hinc1]
  let e := (mulLeft (R := AF F) (d := d) (incM F P⁻¹) (incM F P) h1 h2).trans (glue M₁.co.e p q)
  have he : ∀ w', e w' = glue M₁.co.e p q (incM F P⁻¹ * w') := fun _ => rfl
  have hrow : ∀ (Z : Matrix (Fin (n₁ + 2)) (Fin d) E) r, incM F Z r = incV F (Z r) := fun _ _ => rfl
  have hembι : ∀ z : Matrix (Fin n₁) (Fin d) (AE F E), incM F H.ι * z = incM F P * emb z 0 0 := fun z => by
    ext r l
    simp [Matrix.mul_apply, Fin.sum_univ_add, emb, incM, hPι]
  have hembx : ∀ z : Fin d → AE F E,
      Matrix.vecMulVec (incV F H.x) z = incM F P * emb (0 : Matrix (Fin n₁) (Fin d) (AE F E)) z 0 := fun z => by
    ext r l
    simp [Matrix.mul_apply, Fin.sum_univ_add, emb, incM, incV, hPx, Matrix.vecMulVec_apply]
  have hemby : ∀ z : Fin d → AE F E,
      Matrix.vecMulVec (incV F H.y) z = incM F P * emb (0 : Matrix (Fin n₁) (Fin d) (AE F E)) 0 z := fun z => by
    ext r l
    simp [Matrix.mul_apply, Fin.sum_univ_add, emb, incM, incV, hPy, Matrix.vecMulVec_apply]
  have hback : ∀ Z : Matrix (Fin (n₁ + 2)) (Fin d) (AE F E), incM F P⁻¹ * (incM F P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hG : (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) = incM F (Pᵀ * X.J * P.map σ) := by
    rw [hinc, hinc]; rfl
  have key : ∀ z z' : Matrix (Fin (n₁ + 2)) (Fin d) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F P * z) (incM F P * z') =
        (e (incM F P * z)).1 ⬝ᵥ (e (incM F P * z')).2 - (e (incM F P * z')).1 ⬝ᵥ (e (incM F P * z)).2 := fun z z' => by
    rw [he, he, hback, hback, glue_form M₁.co.e p q _ M₁.co.form, GlobalTheory.T.symplectic_form_base_change_matrix, hG,
      GlobalTheory.T.hermitian_block_decomposition_hyperbolic σ n₁ d _ X₁.J W.J hG1 hG2 hG3 hG00 hG11 hG01 hG10 z z', hpq (z' (Fin.natAdd n₁ 0)) (z (Fin.natAdd n₁ 1)),
      hpq' (z (Fin.natAdd n₁ 0)) (z' (Fin.natAdd n₁ 1)), map_neg]
    simp only [top]
    ring
  have hnot : ∀ (t : Fin 2) (l : Fin d), ¬∃ k : Fin n₁ × Fin d, (Fin.castAdd 2 k.1, k.2) = (Fin.natAdd n₁ t, l) := by
    rintro t l ⟨k, hk⟩
    have := congrArg (fun x => x.1.val) hk
    simp at this
    omega
  have hinj : Function.Injective (fun k : Fin n₁ × Fin d => (Fin.castAdd 2 k.1, k.2)) := fun k k' h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.castAdd_injective _ _ h.1) h.2
  have hext : ∀ f : Fin n₁ × Fin d → AF F,
      comb f 0 = Function.extend (fun k : Fin n₁ × Fin d => (Fin.castAdd 2 k.1, k.2)) f 0 := fun f => by
    refine comb_ext (fun i l => ?_) (fun t l => ?_)
    · rw [comb_castAdd]; exact (hinj.extend_apply f 0 (i, l)).symm
    · rw [comb_natAdd, Function.extend_apply' _ _ _ (hnot t l)]; rfl
  refine ⟨fun k => (Fin.castAdd 2 k.1, k.2), ⟨e, fun w₁ w₂ => ?_⟩, hinj, fun x => ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · have := key (incM F P⁻¹ * w₁) (incM F P⁻¹ * w₂)
    rwa [← Matrix.mul_assoc, h1, Matrix.one_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul] at this
  · rw [he, ← hinc, glue_apply]
    obtain ⟨y₁, z₁, hM⟩ := hM₁.rat (top (P⁻¹ * x))
    obtain ⟨a, ha⟩ := hqr ((P⁻¹ * x) (Fin.natAdd n₁ 1))
    obtain ⟨b, hb⟩ := hpr ((P⁻¹ * x) (Fin.natAdd n₁ 0))
    refine ⟨comb y₁ a, comb z₁ b, ?_⟩
    rw [show top (incM F (P⁻¹ * x)) = incM F (top (P⁻¹ * x)) from rfl, hM, hrow, hrow, ha, hb]
    ext k <;> rcases k with ⟨i, l⟩ <;> refine Fin.addCases (fun i => ?_) (fun t => ?_) i <;> simp
  · rw [he, hembι, hback, glue_apply, top_emb, emb_zero, emb_one, map_zero, map_zero, hext, hext]
  · rw [he, hembx, hback, glue_apply, top_emb, emb_zero, emb_one, map_zero, map_zero]
    refine ⟨?_, fun k => ?_⟩
    · exact comb_ext (fun i l => by simp) (fun t l => by simp)
    · simp
  · rw [he, hemby, hback, glue_apply, top_emb, emb_zero, emb_one, map_zero, map_zero]
    refine ⟨?_, fun k => ?_⟩
    · exact comb_ext (fun i l => by simp) (fun t l => by simp)
    · simp

end GlobalTheory.AdaptedDarboux
