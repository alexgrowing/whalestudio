import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagColsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryBlockConjugateStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegel

theorem adele_conj_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

section Heis
variable {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {Bf : V → V → R}
  {κ : Type} [Fintype κ]

theorem rho_add (d : Darboux Bf κ) (ψ : AddChar R ℂ) {u v : V}
    (h : (d.e u).1 ⬝ᵥ (d.e v).2 = (d.e v).1 ⬝ᵥ (d.e u).2) (φ : (κ → R) → ℂ) :
    d.rho ψ (u + v) φ = d.rho ψ u (d.rho ψ v φ) := by
  funext x
  simp only [Darboux.rho, schr, map_add, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(⅟(2 : R))) * h + ((d.e u).1 ⬝ᵥ (d.e v).2) * h2
end Heis

section HT
variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [Fintype β]

theorem hTens_vecMulVec (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) (y : α → E) (v : β → E) :
    hTens c JA JB x (Matrix.vecMulVec y v) =
      ∑ i, ∑ k, (x *ᵥ (JB *ᵥ fun l => c (v l))) i * JA i k * c (y k) := by
  simp only [hTens, Matrix.vecMulVec, Matrix.of_apply, map_mul, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end HT

theorem symp_lagCols_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (y₁ y₂ : Fin n → AE F E) (Z : Matrix (Fin n) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))
        (Z * (Matrix.fromRows (incM F H'.ι) (incM F H'.ι))ᵀ) (Matrix.vecMulVec y₁ (Sum.elim (incV F H'.x) 0)) = 0 ∧
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))
        (Z * (Matrix.fromRows (incM F H'.ι) (incM F H'.ι))ᵀ) (Matrix.vecMulVec y₂ (Sum.elim 0 (incV F H'.x))) = 0 ∧
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))
        (Matrix.vecMulVec y₁ (Sum.elim (incV F H'.x) 0)) (Matrix.vecMulVec y₂ (Sum.elim 0 (incV F H'.x))) = 0 := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ hH y₁ y₂ Z
  have hform : ∀ m : Fin d₁, ∑ j, incM F H'.ι j m * ∑ l, incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    intro m
    have h := congrArg (inclR (F := F) (AF F)) (hH.orth (Pi.single m 1)).1
    simp only [form, dotProduct, Matrix.mulVec, Matrix.mulVec_single, map_sum, map_mul, map_zero] at h
    simpa [incM, incV, adele_conj_inclR, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h

  have v1 : (Matrix.fromRows (incM F H'.ι) (incM F H'.ι))ᵀ *ᵥ
      (dbl (incM F W.J) *ᵥ fun l => cA σ (Sum.elim (incV F H'.x) (0 : Fin d → AE F E) l)) = 0 := by
    funext m
    simpa [dbl, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hform m
  have v2 : (Matrix.fromRows (incM F H'.ι) (incM F H'.ι))ᵀ *ᵥ
      (dbl (incM F W.J) *ᵥ fun l => cA σ (Sum.elim (0 : Fin d → AE F E) (incV F H'.x) l)) = 0 := by
    funext m
    simpa [dbl, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hform m
  have v3 : Matrix.vecMulVec y₁ (Sum.elim (incV F H'.x) (0 : Fin d → AE F E)) *ᵥ
      (dbl (incM F W.J) *ᵥ fun l => cA σ (Sum.elim (0 : Fin d → AE F E) (incV F H'.x) l)) = 0 := by
    funext i
    simp [dbl, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.vecMulVec]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [symp, hTens_vecMulVec, ← Matrix.mulVec_mulVec, v1, v2, v3, Matrix.mulVec_zero, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, mul_zero, map_zero]

theorem siegelRule_transport : ∀ (R E : Type) [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (C : TestClass R)
    (ψ : AddChar R ℂ) (ξ : E) (α β κ ν ν' : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    [Fintype ν] [DecidableEq ν] [Fintype ν'] [DecidableEq ν'] (JA : Matrix α α E) (JB : Matrix β β E)
    (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle) (Cy : Matrix β ν E) (Cy' : Matrix β ν' E)
    (om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)),
    IsSplitting C ψ d (actB c) om → SiegelRule c C ψ ξ JA JB d χ Cy om →
    ∀ (γ : UG c JB) (S : Matrix ν' ν E) (S' : Matrix ν ν' E),
      ((γ : GL β E) : Matrix β β E) * Cy = Cy' * S → S * S' = 1 → S' * S = 1 →
      SiegelRule c C ψ ξ JA JB d χ Cy' om := by
  intro R E _ _ _ _ c C ψ ξ α β κ ν ν' _ _ _ _ _ _ _ _ _ JA JB d χ Cy Cy' om hS hSR γ S S' hγ hSS' hS'S
  intro l hl hinv p T hp φ hφ
  have hl' : l ∘ₗ om γ ∈ C.adm κ := hS.adm γ l hl
  have hinv' : ∀ z : Matrix α ν E, ∀ φ ∈ C.sp κ, (l ∘ₗ om γ) (d.rho ψ (z * Cyᵀ) φ) = (l ∘ₗ om γ) φ := by
    intro z φ hφ
    simp only [LinearMap.comp_apply]
    rw [hS.impl γ _ φ hφ]
    have e : actB c γ (z * Cyᵀ) = (z * Sᵀ) * Cy'ᵀ := by
      simp only [actB]
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hγ, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hinv _ _ (hS.pres γ φ hφ)]
  have hCy' : Cy' = ((γ : GL β E) : Matrix β β E) * Cy * S' := by
    rw [hγ, Matrix.mul_assoc, hSS', Matrix.mul_one]
  let t' : GL ν E := ⟨S' * (T : Matrix ν' ν' E) * S, S' * ((T⁻¹ : GL ν' E) : Matrix ν' ν' E) * S, by
      rw [show S' * (T : Matrix ν' ν' E) * S * (S' * ((T⁻¹ : GL ν' E) : Matrix ν' ν' E) * S) =
        S' * ((T : Matrix ν' ν' E) * (S * S') * ((T⁻¹ : GL ν' E) : Matrix ν' ν' E)) * S by
          simp only [Matrix.mul_assoc]]
      rw [hSS', Matrix.mul_one, Units.mul_inv, Matrix.mul_one, hS'S], by
      rw [show S' * ((T⁻¹ : GL ν' E) : Matrix ν' ν' E) * S * (S' * (T : Matrix ν' ν' E) * S) =
        S' * (((T⁻¹ : GL ν' E) : Matrix ν' ν' E) * (S * S') * (T : Matrix ν' ν' E)) * S by
          simp only [Matrix.mul_assoc]]
      rw [hSS', Matrix.mul_one, Units.inv_mul, Matrix.mul_one, hS'S]⟩
  have hp' : (((γ⁻¹ * p * γ : UG c JB) : GL β E) : Matrix β β E) * Cy = Cy * (t' : Matrix ν ν E) := by
    have e1 : (((γ⁻¹ * p * γ : UG c JB) : GL β E) : Matrix β β E) =
        (((γ⁻¹ : UG c JB) : GL β E) : Matrix β β E) * ((p : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) := rfl
    have e2 : (((γ⁻¹ : UG c JB) : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    have e4 : (((γ⁻¹ : UG c JB) : GL β E) : Matrix β β E) * ((p : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) * Cy =
        (((γ⁻¹ : UG c JB) : GL β E) : Matrix β β E) * (((p : GL β E) : Matrix β β E) * Cy') * S := by
      rw [Matrix.mul_assoc (_ * _), hγ]; simp only [Matrix.mul_assoc]
    rw [e1, e4, hp, hCy']
    show _ = Cy * (S' * (T : Matrix ν' ν' E) * S)
    simp only [← Matrix.mul_assoc]
    rw [e2, Matrix.one_mul]
  have hdet : Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det T := by
    ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    show (S' * (T : Matrix ν' ν' E) * S).det = _
    rw [Matrix.mul_assoc, Matrix.det_comm' hS'S hSS', Matrix.mul_assoc, hSS', Matrix.mul_one]
  have key := hSR (l ∘ₗ om γ) hl' hinv' (γ⁻¹ * p * γ) t' hp' (om γ⁻¹ φ) (hS.pres _ _ hφ)
  rw [hdet] at key
  simp only [LinearMap.comp_apply] at key
  have e3 : ∀ g h : UG c JB, om g (om h φ) = om (g * h) φ := fun g h => by rw [map_mul]; rfl
  rw [e3, e3, e3] at key
  simpa using key

section Mat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem lagCols_eq {n d d₁ : ℕ} (x : Fin d → AE F E) (ι : Matrix (Fin d) (Fin d₁) (AE F E))
    (z : Matrix (Fin n) (Fin 2 ⊕ Fin d₁) (AE F E)) :
    z * (lagCols x ι)ᵀ = Matrix.vecMulVec (fun i => z i (Sum.inl 0)) (Sum.elim x 0) +
      Matrix.vecMulVec (fun i => z i (Sum.inl 1)) (Sum.elim 0 x) +
      Matrix.of (fun i m => z i (Sum.inr m)) * (Matrix.fromRows ι ι)ᵀ := by
  ext i (j | j) <;> simp [lagCols, Matrix.mul_apply, Matrix.vecMulVec, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem fromRows_eq {n d d₁ : ℕ} (ι : Matrix (Fin d) (Fin d₁) (AE F E)) (Z : Matrix (Fin n) (Fin d₁) (AE F E)) :
    Z * (Matrix.fromRows ι ι)ᵀ =
      (Z * (diagCols (Fin d₁) : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁) (AE F E))ᵀ) * (Matrix.fromBlocks ι 0 0 ι)ᵀ := by
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, diagCols, Matrix.fromBlocks_mul_fromRows]
  simp

theorem vecMulVec_inl {n d : ℕ} (y : Fin n → AE F E) (x : Fin d → AE F E) :
    Matrix.vecMulVec y (Sum.elim x (0 : Fin d → AE F E)) = Matrix.fromCols (Matrix.vecMulVec y x) 0 := by
  ext i (j | j) <;> simp [Matrix.vecMulVec]

theorem vecMulVec_inr {n d : ℕ} (y : Fin n → AE F E) (x : Fin d → AE F E) :
    Matrix.vecMulVec y (Sum.elim (0 : Fin d → AE F E) x) = Matrix.fromCols 0 (Matrix.vecMulVec y x) := by
  ext i (j | j) <;> simp [Matrix.vecMulVec]
end Mat

theorem inv_lagCols {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hψ : IsStd B.ψ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
    (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ))
    (hheis : ∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ))
    (hinv : ∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
      Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ)
    (hmaps : ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
    (l₁ : ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl₁ : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁),
      l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d₁) : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁) (AE F E))ᵀ) φ) = l₁ φ)
    (z : Matrix (Fin n) (Fin 2 ⊕ Fin d₁) (AE F E)) (Ψ : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)
    (hΨ : Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d)) :
    l₁ (Ed (dd.rho B.ψ (z * (lagCols (incV F H'.x) (incM F H'.ι))ᵀ) Ψ)) = l₁ (Ed Ψ) := by
  set a := Matrix.vecMulVec (fun i => z i (Sum.inl 0)) (Sum.elim (incV F H'.x) (0 : Fin d → AE F E))
  set b := Matrix.vecMulVec (fun i => z i (Sum.inl 1)) (Sum.elim (0 : Fin d → AE F E) (incV F H'.x))
  set Z : Matrix (Fin n) (Fin d₁) (AE F E) := Matrix.of (fun i m => z i (Sum.inr m))
  set c := Z * (Matrix.fromRows (incM F H'.ι) (incM F H'.ι))ᵀ
  have hz : z * (lagCols (incV F H'.x) (incM F H'.ι))ᵀ = a + b + c := lagCols_eq _ _ z
  obtain ⟨P1, P2, P3⟩ := symp_lagCols_eq_zero F E σ B n d d₁ X W W₁ H' i₀ i₁ hH (fun i => z i (Sum.inl 0)) (fun i => z i (Sum.inl 1)) Z
  have f1 := dd.form c a
  have f2 := dd.form c b
  have f3 := dd.form a b
  rw [P1] at f1; rw [P2] at f2; rw [P3] at f3
  have hab : (dd.e (a + b)).1 ⬝ᵥ (dd.e c).2 = (dd.e c).1 ⬝ᵥ (dd.e (a + b)).2 := by
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination f1 + f2
  have hab' : (dd.e a).1 ⬝ᵥ (dd.e b).2 = (dd.e b).1 ⬝ᵥ (dd.e a).2 := by linear_combination -f3
  have hsch : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), dd.rho B.ψ w Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
    fun w Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ (dd.e w) Φ hΦ
  rw [hz, rho_add dd B.ψ hab, rho_add dd B.ψ hab']
  have hc : c = (Z * (diagCols (Fin d₁) : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁) (AE F E))ᵀ) *
      (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ := fromRows_eq _ Z
  have ha : a = Matrix.fromCols (Matrix.vecMulVec (fun i => z i (Sum.inl 0)) (incV F H'.x)) 0 := vecMulVec_inl _ _
  have hb : b = Matrix.fromCols 0 (Matrix.vecMulVec (fun i => z i (Sum.inl 1)) (incV F H'.x)) := vecMulVec_inr _ _
  have hcΨ := hsch c Ψ hΨ
  have hbcΨ := hsch b _ hcΨ
  rw [ha, (hinv _ _ hbcΨ).1, hb, (hinv _ _ hcΨ).2, hc, hheis _ _ hΨ, hl₁ _ _ (hmaps Ψ hΨ)]

theorem blk_diagCols {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d d₁ : ℕ}
    (ι : Matrix (Fin d) (Fin d₁) (AE F E)) :
    Matrix.fromBlocks ι 0 0 ι * (diagCols (Fin d₁) : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁) (AE F E)) = Matrix.fromRows ι ι := by
  rw [diagCols, Matrix.fromBlocks_mul_fromRows]
  simp

theorem modu_pow_ne_zero {R : Type} [CommRing R] (C : TestClass R) (u : Rˣ) (k : ℝ) :
    ((((C.modu u : ℝ) ^ k : ℝ)) : ℂ) ≠ 0 := by
  have h : C.modu u ≠ 0 := (IsUnit.map C.modu (Group.isUnit u)).ne_zero
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h)) k).ne'

theorem scalar_eq_one : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      ∀ (dd₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W₁.J))) (Fin n × Fin d₁ ⊕ Fin n × Fin d₁))
        (omd₁ : UG (cA σ) (dbl (incM F W₁.J)) →* Module.End ℂ ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W₁.J) M₁.co dd₁ →
        IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W₁.J)) dd₁ χX (diagCols (Fin d₁)) omd₁ →
      ∀ (Ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d₁ ⊕ Fin n × Fin d₁ → AF F) → ℂ)),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ∈ schA F (Fin n × Fin d₁ ⊕ Fin n × Fin d₁)) →
        (∀ (z : Matrix (Fin n) (Fin d₁ ⊕ Fin d₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (z * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ) = dd₁.rho B.ψ z (Ed Φ)) →
        (∀ (y : Fin n → AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          Ed (dd.rho B.ψ (Matrix.fromCols (Matrix.vecMulVec y (incV F H'.x)) 0) Φ) = Ed Φ ∧
          Ed (dd.rho B.ψ (Matrix.fromCols 0 (Matrix.vecMulVec y (incV F H'.x))) Φ) = Ed Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁ ⊕ Fin n × Fin d₁), l ∘ₗ Ed ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) →
        (∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0) →
      ∀ (p₁ : UG (cA σ) (dbl (incM F W₁.J))) (t₁ : GL (Fin d₁) (AE F E)),
        (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) * diagCols (Fin d₁) = diagCols (Fin d₁) * t₁.1 →
      ∀ g : UG (cA σ) (dbl (incM F W.J)), ((g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) =
          Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι) * (p₁.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.x) (0 : Fin d → AE F E) = Sum.elim (incV F H'.x) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.x) = Sum.elim (0 : Fin d → AE F E) (incV F H'.x) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (incV F H'.y) (0 : Fin d → AE F E) = Sum.elim (incV F H'.y) (0 : Fin d → AE F E) ∧
        (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *ᵥ Sum.elim (0 : Fin d → AE F E) (incV F H'.y) = Sum.elim (0 : Fin d → AE F E) (incV F H'.y)) →
      ∀ a : ℂ, (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed (omd g Φ) = a • omd₁ p₁ (Ed Φ)) → a = 1 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd omd hdd homd dd₁ omd₁
    hdd₁ homd₁ Ed hmaps hheis hinv hadm hne p₁ t₁ hp₁ g hg a ha
  obtain ⟨hg1, hgx0, hg0x, -, -⟩ := hg
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hne
  obtain ⟨l₁, hl₁adm, hl₁inv, w, hw⟩ := GlobalTheory.T.doubled_darboux_coords_compat F E σ (Fin n) (Fin d₁) (Fin n × Fin d₁) B.ψ (incM F X.J) (incM F W₁.J)
    M₁.co dd₁ hψ hdd₁ (Ed Φ₀) (hmaps Φ₀ hΦ₀) hΦ₀ne
  set Φ₁ := dd.rho B.ψ (w * (Matrix.fromBlocks (incM F H'.ι) 0 0 (incM F H'.ι))ᵀ) Φ₀ with hΦ₁def
  have hΦ₁ : Φ₁ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ Φ₀ hΦ₀
  have hL0 : l₁ (Ed Φ₁) ≠ 0 := by rw [hΦ₁def, hheis w Φ₀ hΦ₀]; exact hw
  obtain ⟨γ, S, S', hγ, hSS', hS'S⟩ := GlobalTheory.T.doubled_unitary_block_conjugate F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hP.skew hP₁.skew hH
  have hSR := siegelRule_transport (AF F) (AE F E) (cA σ) (adeleClass F) B.ψ (-1) (Fin n) (Fin d ⊕ Fin d) (Fin n × Fin d ⊕ Fin n × Fin d)
    (Fin d) (Fin 2 ⊕ Fin d₁) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d))
    (lagCols (incV F H'.x) (incM F H'.ι)) omd homd.2.1.toIsSplitting homd.2.2 γ S S' hγ hSS' hS'S
  let T : GL (Fin 2 ⊕ Fin d₁) (AE F E) := ⟨Matrix.fromBlocks 1 0 0 t₁.1, Matrix.fromBlocks 1 0 0 (t₁⁻¹).1,
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩
  have hT : Matrix.GeneralLinearGroup.det T = Matrix.GeneralLinearGroup.det t₁ := by
    ext
    simp [T, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fromBlocks_zero₂₁]
  have hgA : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (Matrix.of fun r k => ![Sum.elim (incV F H'.x) (0 : Fin d → AE F E), Sum.elim (0 : Fin d → AE F E) (incV F H'.x)] k r) =
      Matrix.of fun r k => ![Sum.elim (incV F H'.x) (0 : Fin d → AE F E), Sum.elim (0 : Fin d → AE F E) (incV F H'.x)] k r := by
    ext r k
    fin_cases k
    · exact congrFun hgx0 r
    · exact congrFun hg0x r
  have hgD : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * Matrix.fromRows (incM F H'.ι) (incM F H'.ι) =
      Matrix.fromRows (incM F H'.ι) (incM F H'.ι) * t₁.1 := by
    rw [← blk_diagCols, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc]
    erw [hp₁]
    exact (Matrix.mul_assoc _ _ _).symm
  have hgT : (g.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) * lagCols (incV F H'.x) (incM F H'.ι) =
      lagCols (incV F H'.x) (incM F H'.ι) * (T : Matrix (Fin 2 ⊕ Fin d₁) (Fin 2 ⊕ Fin d₁) (AE F E)) := by
    simp only [lagCols, T, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hgA, hgD]
    simp
  have hL := hSR (l₁ ∘ₗ Ed) (hadm l₁ hl₁adm)
    (fun z φ hφ => inv_lagCols hH hψ dd dd₁ Ed hheis hinv hmaps l₁ hl₁inv z φ hφ) g T hgT Φ₁ hΦ₁
  have h1 := homd₁.2.2 l₁ hl₁adm hl₁inv p₁ t₁ hp₁ (Ed Φ₁) (hmaps Φ₁ hΦ₁)
  have h2 := congrArg l₁ (ha Φ₁ hΦ₁)
  rw [hT] at hL
  simp only [LinearMap.comp_apply] at hL
  rw [map_smul, smul_eq_mul, h1, hL] at h2
  have hK : (χX (Matrix.GeneralLinearGroup.det t₁) : ℂ) *
      ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t₁)) : ℝ) ^
        ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) * l₁ (Ed Φ₁) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (modu_pow_ne_zero _ _ _)) hL0
  have := mul_right_cancel₀ hK (h2.symm.trans (one_mul _).symm)
  exact this

end GlobalTheory.DblSiegel
