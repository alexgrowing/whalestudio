import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.Transport

variable {n : ℕ}

theorem conj_lie {A B G G' Y : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hY : Y ∈ lieOf G) :
    B * Y * A ∈ lieOf G' := by
  have hY' : Yᴴ * G + G * Y = 0 := hY
  show (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY']; simp

theorem conj_UH {A B G G' g : Mx n} (hAB : A * B = 1) (hG : Aᴴ * G * A = G') (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    B * g * A ∈ Formalism.QuantumDeterminants.UH G' := by
  have hg' : gᴴ * G * g = G := hg
  show (B * g * A)ᴴ * G' * (B * g * A) = G'
  rw [← hG]
  calc (B * g * A)ᴴ * (Aᴴ * G * A) * (B * g * A)
      = Aᴴ * (gᴴ * (A * B)ᴴ * G * (A * B) * g) * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, hg']

theorem prod_conj {Q : Mx n} (h1 : Q⁻¹ * Q = 1) (h2 : Q * Q⁻¹ = 1) (l : List (Mx n)) :
    (l.map fun x => Q * x * Q⁻¹).prod = Q * l.prod * Q⁻¹ := by
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc Q * a * Q⁻¹ * (Q * l.prod * Q⁻¹) = Q * a * (Q⁻¹ * Q) * l.prod * Q⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exp_smul_conj {Q : Mx n} (hQ : IsUnit Q) (X : Mx n) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Q⁻¹)) = Q * NormedSpace.exp (t • X) * Q⁻¹ := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

theorem hasType_transport : ∀ (n : ℕ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ₁ : Mx n → (H →L[ℂ] H)) (σ₂ : Mx n → (H' →L[ℂ] H')) (G₁ G₂ Q : Mx n), IsUnit G₁ → IsUnit Q → Qᴴ * G₂ * Q = G₁ → ∀ U : H ≃ₗᵢ[ℂ] H', (∀ g ∈ Formalism.QuantumDeterminants.UH G₁, ∀ v, U (σ₁ g v) = σ₂ (Q * g * Q⁻¹) (U v)) → ∀ f : Mx n → ℂ, HasType (lieOf G₁) (Formalism.QuantumDeterminants.UH G₁) σ₁ f → HasType (lieOf G₂) (Formalism.QuantumDeterminants.UH G₂) σ₂ (fun y => f (Q⁻¹ * y * Q)) := by
  intro n H H' _ _ _ _ σ₁ σ₂ G₁ G₂ Q hG hQ hGG U hU f hf
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ)
  have h2 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hQ)
  have hGG' : (Q⁻¹)ᴴ * G₁ * Q⁻¹ = G₂ := by
    rw [← hGG]
    calc (Q⁻¹)ᴴ * (Qᴴ * G₂ * Q) * Q⁻¹ = (Q * Q⁻¹)ᴴ * G₂ * (Q * Q⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  have cd : ∀ Y : Mx n, Q * (Q⁻¹ * Y * Q) * Q⁻¹ = Y := fun Y => by
    calc Q * (Q⁻¹ * Y * Q) * Q⁻¹ = (Q * Q⁻¹) * Y * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2]; simp
  let Ur : H ≃L[ℝ] H' :=
    { U.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := U.continuous
      continuous_invFun := U.symm.continuous }
  have hUr : ∀ x, Ur x = U x := fun _ => rfl
  have key : ∀ (k : ℕ) (Xs : Fin k → Mx n), (∀ i, Xs i ∈ lieOf G₁) → ∀ w : H,
      (fun t : Fin k → ℝ => σ₂ (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Q⁻¹))).prod (U w)) =
        Ur ∘ fun t : Fin k → ℝ => σ₁ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod w := by
    intro k Xs hX w
    funext t
    have hm : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G₁ :=
      GlobalTheory.GardingVec.list_prod_mem _ (by
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
        exact GlobalTheory.GardingVec.exp_mem hG (hX i) _)
    rw [Function.comp_apply, hUr, hU _ hm, ← prod_conj h1 h2, List.map_ofFn]
    simp only [exp_smul_conj hQ, Function.comp_def]
  have smF : ∀ w, SmoothVec (lieOf G₁) σ₁ w → SmoothVec (lieOf G₂) σ₂ (U w) := by
    intro w hw k Ys hY
    have hX : ∀ i, Q⁻¹ * Ys i * Q ∈ lieOf G₁ := fun i => conj_lie h2 hGG (hY i)
    have := key k _ hX w
    simp only [cd] at this
    rw [this]
    exact Ur.contDiff.comp (hw k _ hX)
  have smB : ∀ w, SmoothVec (lieOf G₂) σ₂ (U w) → SmoothVec (lieOf G₁) σ₁ w := by
    intro w hw k Xs hX
    have := hw k _ fun i => conj_lie h1 hGG' (hX i)
    rw [key k Xs hX w] at this
    exact Ur.comp_contDiff_iff.1 this
  have hd : ∀ X ∈ lieOf G₁, ∀ w, dRep σ₂ (Q * X * Q⁻¹) (U w) = U (dRep σ₁ X w) := by
    intro X hX w
    have e : (fun t : ℝ => σ₂ (NormedSpace.exp (t • (Q * X * Q⁻¹))) (U w)) =
        Ur ∘ fun t : ℝ => σ₁ (NormedSpace.exp (t • X)) w := by
      funext t
      rw [Function.comp_apply, hUr, hU _ (GlobalTheory.GardingVec.exp_mem hG hX t), exp_smul_conj hQ]
    unfold dRep
    rw [e, deriv, deriv, Ur.comp_fderiv]
    rfl
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieOf G₁) → ∀ w,
      (l.map fun X => Q * X * Q⁻¹).foldr (dRep σ₂) (U w) = U (l.foldr (dRep σ₁) w) := by
    intro l hl w
    induction l with
    | nil => rfl
    | cons X l ih =>
      rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY),
        hd X (hl X List.mem_cons_self)]
  obtain ⟨S, hS, ⟨B, hB, hBc⟩, v, ℓ, C, e1, e2, e3, e4, e5⟩ := hf
  have hs : ∀ w, sobNorm σ₂ (S.map fun l => l.map fun X => Q * X * Q⁻¹) (U w) = sobNorm σ₁ S w := by
    intro w
    unfold sobNorm
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    simp only [Function.comp_apply]
    rw [hw l (hS l hl), U.norm_map]
  have hσ : ∀ g ∈ Formalism.QuantumDeterminants.UH G₂, ∀ w, σ₂ g (U w) = U (σ₁ (Q⁻¹ * g * Q) w) := fun g hg w => by
    rw [hU _ (conj_UH h2 hGG hg), cd]
  refine ⟨S.map fun l => l.map fun X => Q * X * Q⁻¹, ?_, ⟨fun y => B (Q⁻¹ * y * Q), hB.comp (by fun_prop), ?_⟩,
    fun i => U (v i), fun i => ℓ i ∘ₗ (U.symm.toLinearEquiv : H' →ₗ[ℂ] H), C, fun i => smF _ (e1 i), e2, ?_, ?_, ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 hGG' (hS l' hl' Y hY)
  · intro g hg w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hσ g hg, hs, hs]
    exact hBc _ (conj_UH h2 hGG hg) w (smB w hw')
  · intro i w hw'
    obtain ⟨w, rfl⟩ := U.surjective w
    rw [hs]
    simpa using e3 i w (smB w hw')
  · simpa only [hs] using e4
  · intro g hg
    simpa [hσ g hg] using e5 _ (conj_UH h2 hGG hg)

end GlobalTheory.TypeSum.Transport
