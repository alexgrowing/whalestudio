import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AutomorphicArithmetic.DivisorFrames.ThetaPairPlaneCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMovesYByIotaAndX
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

section
open GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem cA_inclR' (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

private theorem hA_add_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, Pi.add_apply, map_add]
  rw [show (fun i => cA σ (w i) + cA σ (w' i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) from rfl,
    Matrix.mulVec_add, dotProduct_add]

private theorem hA_smul_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) (β : AE F E) :
    hA σ J v (β • w) = cA σ β * hA σ J v w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => cA σ β * cA σ (w i)) = cA σ β • (fun i => cA σ (w i)) from rfl, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

private theorem hA_incV' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    hA σ J (incV F v) (incV F w) = inclR (F := F) (AF F) (form σ J v w) := by
  simp only [hA, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, cA_inclR']

private theorem incM_mulVec_incV' {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i
  simp only [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

private theorem cA_mulVec_incM (σ : E →ₐ[F] E) {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (z : Fin n → AE F E) :
    (fun i => cA σ ((incM F A *ᵥ z) i)) = incM F (A.map σ) *ᵥ fun i => cA σ (z i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, incM, Matrix.map_apply, cA_inclR']

private theorem hA_incM (σ : E →ₐ[F] E) {m n : ℕ} (J : Matrix (Fin m) (Fin m) E) (A : Matrix (Fin m) (Fin n) E)
    (a z : Fin n → AE F E) :
    hA σ J (incM F A *ᵥ a) (incM F A *ᵥ z) = hA σ (Aᵀ * J * A.map σ) a z := by
  unfold hA
  rw [cA_mulVec_incM, Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.mulVec_mulVec]
  congr 2
  simp [incM, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]

private theorem phase_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (u : UA σ W.J) (w : Fin d₁ → E) (z : Fin d₁ → AE F E) (β : AE F E),
      mat u⁻¹ *ᵥ incV F H'.y = incV F H'.y + incM F H'.ι *ᵥ z + β • incV F H'.x →
      GlobalTheory.IsoPhase.phase σ W H' w u = -Algebra.trace (AF F) (AE F E) (GlobalTheory.UnipMass.hA σ W₁.J (incV F w) z) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ hH u w z β hu
  unfold GlobalTheory.IsoPhase.phase
  rw [hu, hA_add_right', hA_add_right', hA_smul_right', hA_incV', hA_incV', (hH.orth w).1, (hH.orth w).2,
    ← incM_mulVec_incV', hA_incM, hH.gram]
  simp

end

private theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = ψ (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) • schr ψ b (schr ψ a φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  have hx : x + a.1 + b.1 = x + b.1 + a.1 := by abel
  rw [hx]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  ring

private theorem rho_comm {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}
    {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (a b : W) (φ : (κ → R) → ℂ) :
    d.rho ψ a (d.rho ψ b φ) = ψ (B a b) • d.rho ψ b (d.rho ψ a φ) := by
  rw [d.form]
  exact schr_comm ψ (d.e a) (d.e b) φ

private theorem thetaSum_smul {F : Type} [Field F] [NumberField F] {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

private theorem hTens_vmv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (p p' : α → A) (q q' : β → A) :
    hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q') =
      (p ⬝ᵥ JA *ᵥ fun k => c (p' k)) * (q ⬝ᵥ JB *ᵥ fun l => c (q' l)) := by
  calc hTens c JA JB (Matrix.vecMulVec p q) (Matrix.vecMulVec p' q')
      = ∑ i, ∑ j, ∑ k, ∑ l, (p i * JA i k * c (p' k)) * (q j * JB j l * c (q' l)) := by
        simp only [hTens, Matrix.vecMulVec_apply, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [dotProduct, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem UpperTheory.pair_restricts_along_adapted_plane :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
                 (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (M : Model σ X W) (M₂ : Model σ X₁ W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
                 (χX χW : Chr F E) (om : Rep σ X W) (om₂ : Rep σ X₁ W) (r s r₁ s₁ r' s' : ℕ),
                 IsPair B M χX χW om r s r' s' → IsPair B M₂ χX χW om₂ r₁ s₁ r' s' → H.IsAdapted σ B X X₁ j₀ j₁ →
                 ∀ e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d, IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
                 ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₃ : Model σ X₁ W₁), H'.IsAdapted σ B W W₁ i₀ i₁ →
                 ∀ e₀ : Fn F n₁ d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₂ M₃ 1 H'.ι (iso0 n₁ H') e₀ → ∀ (ξ : Fin n₁ → E), ∀ u ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d),
                   thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
                       (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u, 1) Ψ))))) =
                     B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ u) * thetaSum F (e₀ (M₂.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y))
                       (e₁ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)))) := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he d₁ W₁ H' i₀ i₁ M₃ hH'
    e₀ he₀ ξ u hu Ψ hΨ
  have hstd : IsStd B.ψ := hP.base.std
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.ThK.UnipDom.Inverse.sigma_sigma hP.base.cm
  have hu' : u⁻¹ ∈ unip σ X H := inv_mem hu
  rw [GlobalTheory.UnipCT.unip_eq] at hu'
  obtain ⟨β, z, hv0⟩ := GlobalTheory.UnipLine.mulVec_y hH hP.herm u⁻¹ hu'.1
  have hv : mat u⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ z + β • incV F H.x := by rw [hv0]; abel
  have hm := UpperTheory.theta_pair_plane_compat hKP F E σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ he u hu z β hv
    (incV F H'.x) Ψ hΨ
  rw [hA_incV', hH'.xx, map_zero, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_smul] at hm
  have hφs := he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ hΨ)
  have hφ' := GlobalTheory.HeisSchA.rho_mem_schA M₂ B.ψ hstd (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) _ hφs
  have hyx : GlobalTheory.UnipMass.hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [hA_incV', GlobalTheory.IsoMove.form_y_x hσ hP.skew.skew hH', map_neg, map_one]
  rw [hm, rho_comm, map_smul, he₀.inv _ ⟨z, rfl⟩ _ hφ', thetaSum_smul,
    phase_eq F E σ B n n₁ X X₁ H j₀ j₁ hH u ξ z β hv, neg_neg, symp, hTens_vmv]
  congr 3
  change -1 * (GlobalTheory.UnipMass.hA σ X₁.J (incV F ξ) z * GlobalTheory.UnipMass.hA σ W.J (incV F H'.y) (incV F H'.x)) = _
  rw [hyx]
  ring
