import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.ThK.AdaptEv.VacIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_add_left' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x x' y : Matrix α β A) :
    hTens c JA JB (x + x') y = hTens c JA JB x y + hTens c JA JB x' y := by
  simp only [hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hTens_add_right' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y y' : Matrix α β A) :
    hTens c JA JB x (y + y') = hTens c JA JB x y + hTens c JA JB x y' := by
  simp only [hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hTens_pure {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin d → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem sum_vv (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (u v : Fin d → E) :
    (∑ j, ∑ l, incV F u j * incM F J j l * cA σ (incV F v l)) = inclR (F := F) (AF F) (form σ J u v) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum, mul_assoc]

theorem sum_vm (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (u : Fin d → E)
    (ι : Matrix (Fin d) (Fin d₁) E) (z : Fin d₁ → AE F E) :
    (∑ j, ∑ l, incV F u j * incM F J j l * cA σ ((incM F ι *ᵥ z) l)) =
      ∑ m, inclR (F := F) (AF F) (form σ J u (fun l => ι l m)) * cA σ (z m) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem sum_mv (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (v : Fin d → E)
    (ι : Matrix (Fin d) (Fin d₁) E) (z : Fin d₁ → AE F E) :
    (∑ j, ∑ l, (incM F ι *ᵥ z) j * incM F J j l * cA σ (incV F v l)) =
      ∑ m, z m * inclR (F := F) (AF F) (form σ J (fun j => ι j m) v) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  refine ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isotropic_key (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n d d₁ : ℕ} (JX : Matrix (Fin n) (Fin n) E)
    (JW : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (JW j i) = -JW i j) (x₀ : Fin n → E) (w₀ : Fin d → E)
    (ι : Matrix (Fin d) (Fin d₁) E) (hx : form σ JX x₀ x₀ = 0) (hw : form σ JW w₀ w₀ = 0)
    (ho : ∀ u, form σ JW (ι *ᵥ u) w₀ = 0) (y : Fin n → AE F E) (z : Fin d₁ → AE F E) :
    hTens (cA σ) (incM F JX) (incM F JW)
      (Matrix.vecMulVec y (incV F w₀) + Matrix.vecMulVec (incV F x₀) (incM F ι *ᵥ z))
      (Matrix.vecMulVec y (incV F w₀) + Matrix.vecMulVec (incV F x₀) (incM F ι *ᵥ z)) = 0 := by
  have hcol : ∀ m, ι *ᵥ Pi.single m 1 = fun j => ι j m := fun m => by
    ext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have col : ∀ m, form σ JW (fun j => ι j m) w₀ = 0 := fun m => by rw [← hcol]; exact ho _
  have col' : ∀ m, form σ JW w₀ (fun j => ι j m) = 0 := fun m => by
    rw [form_swap hσ hJ, col m, map_zero, neg_zero]
  have hX : (∑ i, ∑ k, incV F x₀ i * incM F JX i k * cA σ (incV F x₀ k)) = 0 := by
    rw [sum_vv, hx, map_zero]
  have hWW : (∑ j, ∑ l, incV F w₀ j * incM F JW j l * cA σ (incV F w₀ l)) = 0 := by
    rw [sum_vv, hw, map_zero]
  have hWm : (∑ j, ∑ l, incV F w₀ j * incM F JW j l * cA σ ((incM F ι *ᵥ z) l)) = 0 := by
    rw [sum_vm]; simp [col']
  have hmW : (∑ j, ∑ l, (incM F ι *ᵥ z) j * incM F JW j l * cA σ (incV F w₀ l)) = 0 := by
    rw [sum_mv]; simp [col]
  rw [hTens_add_left', hTens_add_right', hTens_add_right', hTens_pure, hTens_pure, hTens_pure, hTens_pure,
    hX, hWW, hWm, hmW]
  simp

theorem invol_of_isGood {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) : ∀ e, σ (σ e) = e := by
  intro e
  let τ : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have h := hB.cm.2.2.2 τ.toRingHom
  apply τ.toRingHom.injective
  rw [h, h, star_star]

end GlobalTheory.ThK.AdaptEv.VacIso

open GlobalTheory.ThK.AdaptEv.VacIso in

theorem GlobalTheory.ThK.AdaptEv.VacIso.spans_isotropic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (r' s' i₀ i₁ j₀ j₁ : ℕ), (∀ e, σ (σ e) = e) → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (∀ p ∈ GlobalTheory.ThK.AdaptEv.VacuumBlock.spanA (F := F) H H', hTens (cA σ) (incM F X.J) (incM F W.J) p p = 0) ∧
      ∀ q ∈ GlobalTheory.ThK.AdaptEv.VacuumBlock.spanAd (F := F) H H', hTens (cA σ) (incM F X.J) (incM F W.J) q q = 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r' s' i₀ i₁ j₀ j₁ hσ hW hH hH'
  refine ⟨?_, ?_⟩
  · rintro p ⟨y, z, rfl⟩
    exact isotropic_key σ hσ X.J W.J hW.skew H.x H'.x H'.ι hH.xx hH'.xx (fun u => (hH'.orth u).1) y z
  · rintro q ⟨y, z, rfl⟩
    exact isotropic_key σ hσ X.J W.J hW.skew H.y H'.y H'.ι hH.yy hH'.yy (fun u => (hH'.orth u).2) y z
