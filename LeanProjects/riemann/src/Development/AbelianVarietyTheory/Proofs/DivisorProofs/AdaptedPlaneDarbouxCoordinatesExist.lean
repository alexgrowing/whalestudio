import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneBasisChangeMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicBasisMatrixGramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRightMulTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGramMatrixOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTraceFormCoordinatesStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section
namespace GlobalTheory.ThK.PlaneEv.Coords

section Glue

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n d₁ : ℕ}

def colSplit : Matrix (Fin n) (Fin (d₁ + 2)) A ≃ₗ[R] Matrix (Fin n) (Fin d₁) A × ((Fin n → A) × (Fin n → A)) where
  toFun Y := (Matrix.of fun i a => Y i (Fin.castAdd 2 a), (fun i => Y i (Fin.natAdd d₁ 1), fun i => Y i (Fin.natAdd d₁ 0)))
  invFun w := Matrix.of fun i c => Fin.addCases (motive := fun _ => A) (fun a => w.1 i a) (fun t => ![w.2.2 i, w.2.1 i] t) c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Y := by
    ext i c
    refine Fin.addCases (fun a => ?_) (fun t => ?_) c
    · simp
    · fin_cases t <;> simp
  right_inv w := by
    rcases w with ⟨Z, b, a⟩
    ext <;> simp

@[simp] theorem colSplit_apply (Y : Matrix (Fin n) (Fin (d₁ + 2)) A) : colSplit (R := R) Y =
    (Matrix.of fun i a => Y i (Fin.castAdd 2 a), (fun i => Y i (Fin.natAdd d₁ 1), fun i => Y i (Fin.natAdd d₁ 0))) := rfl

def glueC (e₁ : Matrix (Fin n) (Fin d₁) A ≃ₗ[R] (Fin n × Fin d₁ → R) × (Fin n × Fin d₁ → R))
    (p q : (Fin n → A) ≃ₗ[R] (Fin n × Fin 2 → R)) :
    Matrix (Fin n) (Fin (d₁ + 2)) A ≃ₗ[R] (Fin n × Fin (d₁ + 2) → R) × (Fin n × Fin (d₁ + 2) → R) :=
  colSplit ≪≫ₗ (e₁.prodCongr (p.prodCongr q)) ≪≫ₗ LinearEquiv.prodProdProdComm R _ _ _ _ ≪≫ₗ
    (((LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm ≪≫ₗ LinearEquiv.funCongrLeft R R (idx rfl)).prodCongr
      ((LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm ≪≫ₗ LinearEquiv.funCongrLeft R R (idx rfl)))

theorem glueC_apply (e₁ : Matrix (Fin n) (Fin d₁) A ≃ₗ[R] (Fin n × Fin d₁ → R) × (Fin n × Fin d₁ → R))
    (p q : (Fin n → A) ≃ₗ[R] (Fin n × Fin 2 → R)) (Y : Matrix (Fin n) (Fin (d₁ + 2)) A) :
    glueC e₁ p q Y = (fun k => Sum.elim (e₁ (Matrix.of fun i a => Y i (Fin.castAdd 2 a))).1 (p fun i => Y i (Fin.natAdd d₁ 1)) (idx rfl k),
      fun k => Sum.elim (e₁ (Matrix.of fun i a => Y i (Fin.castAdd 2 a))).2 (q fun i => Y i (Fin.natAdd d₁ 0)) (idx rfl k)) := by
  ext k <;> simp [glueC, LinearEquiv.funCongrLeft_apply, LinearEquiv.sumArrowLequivProdArrow] <;> rcases idx rfl k with p | p <;> simp

theorem dot_idx (f g : Fin n × Fin d₁ → R) (f' g' : Fin n × Fin 2 → R) :
    (fun k => Sum.elim f f' (idx (n := n) (d := d₁ + 2) rfl k)) ⬝ᵥ (fun k => Sum.elim g g' (idx rfl k)) = f ⬝ᵥ g + f' ⬝ᵥ g' := by
  simp only [dotProduct]
  rw [(idx rfl).sum_comp (fun k => Sum.elim f f' k * Sum.elim g g' k), Fintype.sum_sum_type]
  simp

end Glue

section Emb

variable {A : Type} [Zero A] {n d₁ : ℕ}

def embC (Z : Matrix (Fin n) (Fin d₁) A) (a b : Fin n → A) : Matrix (Fin n) (Fin (d₁ + 2)) A :=
  Matrix.of fun i c => Fin.addCases (motive := fun _ => A) (fun k => Z i k) (fun t => ![a i, b i] t) c

@[simp] theorem embC_left (Z : Matrix (Fin n) (Fin d₁) A) (a b : Fin n → A) :
    (Matrix.of fun i k => embC Z a b i (Fin.castAdd 2 k)) = Z := by
  ext i k; simp [embC]

@[simp] theorem embC_zero (Z : Matrix (Fin n) (Fin d₁) A) (a b : Fin n → A) :
    (fun i => embC Z a b i (Fin.natAdd d₁ 0)) = a := by
  funext i; simp [embC]

@[simp] theorem embC_one (Z : Matrix (Fin n) (Fin d₁) A) (a b : Fin n → A) :
    (fun i => embC Z a b i (Fin.natAdd d₁ 1)) = b := by
  funext i; simp [embC]

end Emb

theorem exists_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁)
    (hd : d = d₁ + 2), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d), ((∀ z : Matrix (Fin n) (Fin d₁) (AE F E), co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (M₁.co.e z).1, ins0 hd (M₁.co.e z).2)) ∧
      (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) ∧
      (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) ∧
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁
  subst hd
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hXdet : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_trace_form_coordinates σ n X.J hσ hB.cm.2.2.1 hX.herm hXdet
  let Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E := Matrix.of fun r c =>
    Fin.addCases (motive := fun _ => E) (fun i => H'.ι r i) (fun t => ![H'.x r, H'.y r] t) c
  have hQι : ∀ r i, Q r (Fin.castAdd 2 i) = H'.ι r i := fun r i => by simp [Q]
  have hQx : ∀ r, Q r (Fin.natAdd d₁ 0) = H'.x r := fun r => by simp [Q]
  have hQy : ∀ r, Q r (Fin.natAdd d₁ 1) = H'.y r := fun r => by simp [Q]
  have hQdet := GlobalTheory.T.adapted_plane_basis_change_matrix F E σ B d₁ r' s' i₀ i₁ W W₁ H' Q hW hH hQι hQx hQy
  obtain ⟨hG1, hG2, hG3, hG00, hG11, hG01, hG10⟩ :=
    GlobalTheory.T.hyperbolic_basis_matrix_gram σ d₁ W.J W₁.J H'.x H'.y H'.ι Q hσ hW.skew hH.xx hH.yy hH.xy hH.orth hH.gram hQι hQx hQy
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (Ne.isUnit hQdet)
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (Ne.isUnit hQdet)
  have hinc : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have hinc1 : incM F (1 : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← hinc, hQQ', hinc1, Matrix.transpose_one]
  have h2 : (incM F Q⁻¹)ᵀ * (incM F Q)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← hinc, hQQ, hinc1, Matrix.transpose_one]
  let mR : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E) ≃ₗ[AF F] Matrix (Fin n) (Fin (d₁ + 2)) (AE F E) :=
    { toFun := fun u => u * (incM F Q⁻¹)ᵀ
      invFun := fun Y => Y * (incM F Q)ᵀ
      map_add' := fun u u' => Matrix.add_mul u u' _
      map_smul' := fun a u => Matrix.smul_mul a u _
      left_inv := fun u => by
        show u * (incM F Q⁻¹)ᵀ * (incM F Q)ᵀ = u
        rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      right_inv := fun Y => by
        show Y * (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = Y
        rw [Matrix.mul_assoc, h1, Matrix.mul_one] }
  let e := mR ≪≫ₗ glueC M₁.co.e p q
  have he : ∀ u, e u = glueC M₁.co.e p q (u * (incM F Q⁻¹)ᵀ) := fun _ => rfl
  have hback : ∀ Y : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E), Y * (incM F Q)ᵀ * (incM F Q⁻¹)ᵀ = Y := fun Y => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hG : (incM F Q)ᵀ * incM F W.J * (incM F Q).map (cA σ) = incM F (Qᵀ * W.J * Q.map σ) := by
    rw [hinc, hinc]; rfl
  have key : ∀ Y Y' : Matrix (Fin n) (Fin (d₁ + 2)) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (Y * (incM F Q)ᵀ) (Y' * (incM F Q)ᵀ) =
        (e (Y * (incM F Q)ᵀ)).1 ⬝ᵥ (e (Y' * (incM F Q)ᵀ)).2 - (e (Y' * (incM F Q)ᵀ)).1 ⬝ᵥ (e (Y * (incM F Q)ᵀ)).2 := fun Y Y' => by
    rw [he, he, hback, hback, glueC_apply, glueC_apply, dot_idx, dot_idx, GlobalTheory.T.symplectic_form_right_mul_transpose, hG,
      GlobalTheory.T.block_gram_matrix_orthogonal_sum (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ (fun a a' => by simp [incM, hG1]) (fun a t => by simp [incM, hG2])
        (fun t a => by simp [incM, hG3]) (by simp [incM, hG00]) (by simp [incM, hG11]) (by simp [incM, hG01])
        (by simp [incM, hG10]) Y Y',
      M₁.co.form, hpq (fun i => Y' i (Fin.natAdd d₁ 0)) (fun i => Y i (Fin.natAdd d₁ 1)),
      hpq' (fun i => Y i (Fin.natAdd d₁ 0)) (fun i => Y' i (Fin.natAdd d₁ 1)), neg_one_mul, neg_one_mul, map_neg, map_neg]
    ring
  refine ⟨⟨e, fun u u' => ?_⟩, fun z => ?_, fun a => ?_, fun b => ?_, fun x => ?_⟩
  · have := key (u * (incM F Q⁻¹)ᵀ) (u' * (incM F Q⁻¹)ᵀ)
    rwa [Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.mul_assoc, h2, Matrix.mul_one] at this
  · have hz : z * (incM F H'.ι)ᵀ = embC z 0 0 * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, hQι]
    rw [hz, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    rfl
  · have ha : Matrix.vecMulVec a (incV F H'.x) = embC (0 : Matrix (Fin n) (Fin d₁) (AE F E)) a 0 * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, incV, hQx, Matrix.vecMulVec_apply]
    rw [ha, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun k => ?_⟩
    · rcases idx rfl k with k | k <;> simp
    · simp
  · have hb : Matrix.vecMulVec b (incV F H'.y) = embC (0 : Matrix (Fin n) (Fin d₁) (AE F E)) 0 b * (incM F Q)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_add, embC, incM, incV, hQy, Matrix.vecMulVec_apply]
    rw [hb, he, hback, glueC_apply, embC_left, embC_zero, embC_one, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun k => ?_⟩
    · rcases idx rfl k with k | k <;> simp
    · simp
  · rw [he, show incM F x * (incM F Q⁻¹)ᵀ = incM F (x * (Q⁻¹)ᵀ) from (hinc _ _).symm, glueC_apply]
    obtain ⟨y₁, z₁, hM⟩ := hM₁.rat (Matrix.of fun i a => (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a))
    obtain ⟨yb, hyb⟩ := hpr (fun i => (x * (Q⁻¹)ᵀ) i (Fin.natAdd d₁ 1))
    obtain ⟨za, hza⟩ := hqr (fun i => (x * (Q⁻¹)ᵀ) i (Fin.natAdd d₁ 0))
    refine ⟨fun k => Sum.elim y₁ yb (idx rfl k), fun k => Sum.elim z₁ za (idx rfl k), ?_⟩
    have e1 : (Matrix.of fun i a => incM F (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a)) =
        incM F (Matrix.of fun i a => (x * (Q⁻¹)ᵀ) i (Fin.castAdd 2 a)) := rfl
    have e2 : ∀ c, (fun i => incM F (x * (Q⁻¹)ᵀ) i c) = incV F (fun i => (x * (Q⁻¹)ᵀ) i c) := fun _ => rfl
    rw [e1, e2, e2, hM, hyb, hza]
    ext k <;> dsimp only <;> rcases idx rfl k with k | k <;> simp

end GlobalTheory.ThK.PlaneEv.Coords
