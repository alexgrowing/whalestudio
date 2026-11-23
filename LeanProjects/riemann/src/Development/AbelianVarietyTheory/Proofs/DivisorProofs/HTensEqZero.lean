import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixW.UnipHeis

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h : a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = schr ψ (a + b) φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [show x + a.1 + b.1 = x + (a.1 + b.1) from add_assoc _ _ _]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  rw [dotProduct_comm b.1 a.2] at h ⊢
  linear_combination (1 - ⅟(2 : R)) * h - (a.2 ⬝ᵥ b.1) * h2

theorem rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : dc.rho ψ w (dc.rho ψ w' φ) = dc.rho ψ (w + w') φ := by
  simp only [Darboux.rho, map_add]
  refine schr_schr ψ _ _ ?_ φ
  have := dc.form w w'
  rw [h] at this
  exact (sub_eq_zero.mp this.symm)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem hTens_eq_zero {n d d₁ : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (ι : Matrix (Fin d) (Fin d₁) E) (x : Fin d → E) (hor : ∀ u, form σ JW (ι *ᵥ u) x = 0)
    (z : Matrix (Fin n) (Fin d₁) (AE F E)) (q : Fin n → AE F E) :
    hTens (cA σ) (incM F JX) (incM F JW) (z * (incM F ι)ᵀ) (Matrix.vecMulVec q (incV F x)) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  set v : Fin d → AE F E := incM F JW *ᵥ fun l => cA σ (incV F x l) with hvdef
  have hv : (incM F ι)ᵀ *ᵥ v = 0 := by
    funext m
    have h0 := congrArg (inclR (F := F) (AF F)) (hor (Pi.single m 1))
    rw [map_zero] at h0
    rw [Pi.zero_apply, ← h0]
    simp [hvdef, form, Matrix.mulVec, dotProduct, incM, incV, map_sum, map_mul, hc, Pi.single_apply]
  have h0 : ∀ i, ∑ j, (z * (incM F ι)ᵀ) i j * ∑ l, incM F JW j l * cA σ (incV F x l) = 0 := by
    intro i
    have := congrFun (show z *ᵥ ((incM F ι)ᵀ *ᵥ v) = 0 by rw [hv, Matrix.mulVec_zero]) i
    rw [Matrix.mulVec_mulVec] at this
    simpa [hvdef, Matrix.mulVec, dotProduct] using this
  unfold hTens
  simp only [Matrix.vecMulVec_apply, map_mul]
  calc _ = ∑ i, ∑ k, incM F JX i k * cA σ (q k) *
        ∑ j, (z * (incM F ι)ᵀ) i j * ∑ l, incM F JW j l * cA σ (incV F x l) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    _ = 0 := by simp [h0]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ (g : UA σ W.J) (t : AE F E), mat g *ᵥ incV F H'.x = t • incV F H'.x →
      (∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, g) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ)) =
          M₁.co.rho B.ψ z (e (om (1, g) Φ))) ∧
      ∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, g) (M.co.rho B.ψ u Φ)) = e (om (1, g) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g t hgx hgι
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hIm : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM]
  have act : ∀ w : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) ((1 : UA σ X.J), g) w = w * (mat g)ᵀ := by
    intro w
    simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
    rfl
  have vmv : ∀ (y : Fin n → AE F E) (v : Fin d → AE F E) (A : Matrix (Fin d) (Fin d) (AE F E)),
      Matrix.vecMulVec y v * Aᵀ = Matrix.vecMulVec y (A *ᵥ v) := by
    intro y v A
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hS.pres ((1 : UA σ X.J), g) Φ hΦ
    choose a ha using fun k : Fin d₁ => hgι (Pi.single k 1)
    have hgi : mat g * incM F H'.ι = incM F H'.ι + Matrix.vecMulVec (incV F H'.x) a := by
      ext j k
      have := congrFun (ha k) j
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
      simpa [Matrix.vecMulVec_apply, mul_comm] using this
    have hw : incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ * (mat g)ᵀ =
        incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ + Matrix.vecMulVec (z *ᵥ a) (incV F H'.x) := by
      rw [hIm, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hgi, Matrix.transpose_add,
        Matrix.mul_add, Matrix.transpose_vecMulVec]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    have h0 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
        (Matrix.vecMulVec (z *ᵥ a) (incV F H'.x)) = 0 := by
      rw [symp, hIm, Matrix.one_mul, hTens_eq_zero (σ := σ) X.J W.J H'.ι H'.x (fun u => (hA.orth u).1), mul_zero, map_zero]
    rw [hS.impl _ _ _ hΦ, act, hw, ← rho_rho M.co B.ψ _ _ h0,
      he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ _ hΨ), he.inv _ ⟨z *ᵥ a, rfl⟩ _ hΨ]
  · obtain ⟨y, rfl⟩ := hu
    rw [hS.impl _ _ _ hΦ, act, vmv, hgx, show Matrix.vecMulVec y (t • incV F H'.x) = Matrix.vecMulVec (t • y) (incV F H'.x) by
      ext i j; simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]; ring]
    exact he.inv _ ⟨t • y, rfl⟩ _ (hS.pres _ _ hΦ)

end GlobalTheory.MixW.UnipHeis
