import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeStabP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipEvLaw

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = schr ψ (a + b) φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  have h2 : (⅟(2 : R)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (a.1 ⬝ᵥ b.2) * h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem rho_add (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (w l : Matrix (Fin n) (Fin d) (AE F E))
    (h : symp (cA σ) (-1) (incM F X.J) (incM F W.J) w l = 0) (φ : Fn F n d) :
    M.co.rho ψ (w + l) φ = M.co.rho ψ w (M.co.rho ψ l φ) := by
  have h' := (M.co.form w l).symm.trans h
  show schr ψ (M.co.e (w + l)) φ = schr ψ (M.co.e w) (schr ψ (M.co.e l) φ)
  rw [map_add, schr_comp ψ _ _ h']

theorem iota_orth (H' : Plane E d d₁) (hH : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0) :
    (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun l => cA σ (incV F H'.x l)) = 0 := by
  have hE : H'.ιᵀ *ᵥ (W.J *ᵥ fun l => σ (H'.x l)) = 0 := by
    funext m
    have := hH (Pi.single m 1)
    simp only [form] at this
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single_one] at this
    rw [Matrix.mulVec_transpose]
    exact this
  have hc : (fun l => cA σ (incV F H'.x l)) = fun l => inclR (F := F) (AF F) (σ (H'.x l)) := funext fun l => by
    simp [incV, cA, inclR, Algebra.TensorProduct.map_tmul]
  have : (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun l => inclR (F := F) (AF F) (σ (H'.x l))) =
      fun i => inclR (F := F) (AF F) ((H'.ιᵀ *ᵥ (W.J *ᵥ fun l => σ (H'.x l))) i) := by
    funext i
    simp only [incM, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  rw [hc, this, hE]
  funext i
  simp

theorem symp_eq_zero (H' : Plane E d d₁) (hH : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0) (ξ : AE F E)
    (JA : Matrix (Fin n) (Fin n) (AE F E)) (A : Matrix (Fin n) (Fin d₁) (AE F E)) (y : Fin n → AE F E) :
    symp (cA σ) ξ JA (incM F W.J) (A * (incM F H'.ι)ᵀ) (Matrix.vecMulVec y (incV F H'.x)) = 0 := by
  set x := A * (incM F H'.ι)ᵀ
  set v := incV F H'.x
  have hq : x *ᵥ (incM F W.J *ᵥ fun l => cA σ (v l)) = 0 := by
    rw [← Matrix.mulVec_mulVec, iota_orth H' hH, Matrix.mulVec_zero]
  have hx : ∀ i, ∑ j, x i j * ∑ l, incM F W.J j l * cA σ (v l) = 0 := fun i => by
    have := congrFun hq i
    simpa [Matrix.mulVec, dotProduct] using this
  have hT : hTens (cA σ) JA (incM F W.J) x (Matrix.vecMulVec y v) = 0 := by
    unfold hTens
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ∑ j, ∑ l, x i j * JA i k * incM F W.J j l * cA σ (Matrix.vecMulVec y v k l) =
        JA i k * cA σ (y k) * ∑ j, x i j * ∑ l, incM F W.J j l * cA σ (v l) := by
      simp only [Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    rw [this, hx i, mul_zero]
  unfold symp
  rw [hT, mul_zero, map_zero]

theorem heis_stabP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g ∈ GlobalTheory.UnipEv.stabilizer₂ σ W H', ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (1, g) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ)) = M₁.co.rho B.ψ z (e (om (1, g) Φ)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH _ e he g hg z Φ hΦ
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hΨ : om (1, g) Φ ∈ schA F (Fin n × Fin d) := hS.pres (1, g) Φ hΦ
  choose a ha using fun m : Fin d₁ => hg.2 (Pi.single m 1)
  have hmat : mat g * incM F H'.ι = incM F H'.ι + Matrix.vecMulVec (incV F H'.x) a := by
    ext i m
    have := congrFun (ha m) i
    rw [Matrix.mulVec_mulVec] at this
    simpa [Matrix.mulVec_single, Matrix.vecMulVec_apply, mul_comm] using this
  set A := incM F (1 : Matrix (Fin n) (Fin n) E) * z
  have hact : actAB (cA σ) ((1, g) : UA σ X.J × UA σ W.J) (A * (incM F H'.ι)ᵀ) =
      A * (incM F H'.ι)ᵀ + Matrix.vecMulVec (A *ᵥ a) (incV F H'.x) := by
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * (A * (incM F H'.ι)ᵀ) * (mat g)ᵀ = _
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hmat, Matrix.transpose_add, Matrix.transpose_vecMulVec,
      Matrix.mul_add, Matrix.mul_vecMulVec]
  have hsymp := symp_eq_zero H' (fun u => (hH.orth u).1) (-1) (incM F X.J) A (A *ᵥ a)
  calc e (om (1, g) (M.co.rho B.ψ (A * (incM F H'.ι)ᵀ) Φ))
      = e (M.co.rho B.ψ (A * (incM F H'.ι)ᵀ + Matrix.vecMulVec (A *ᵥ a) (incV F H'.x)) (om (1, g) Φ)) := by
        rw [hS.impl (1, g) _ Φ hΦ, hact]
    _ = e (M.co.rho B.ψ (A * (incM F H'.ι)ᵀ) (M.co.rho B.ψ (Matrix.vecMulVec (A *ᵥ a) (incV F H'.x)) (om (1, g) Φ))) := by
        rw [rho_add M B.ψ _ _ hsymp]
    _ = M₁.co.rho B.ψ z (e (M.co.rho B.ψ (Matrix.vecMulVec (A *ᵥ a) (incV F H'.x)) (om (1, g) Φ))) :=
        he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΨ)
    _ = M₁.co.rho B.ψ z (e (om (1, g) Φ)) := by
        rw [he.inv _ ⟨A *ᵥ a, rfl⟩ _ hΨ]

end GlobalTheory.UnipEvLaw
