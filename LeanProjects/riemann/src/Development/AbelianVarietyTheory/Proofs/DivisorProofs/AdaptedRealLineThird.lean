import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCompactLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponents
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AdaptedFrameLevi

open Matrix

theorem col_mul {R ι : Type} [CommRing R] [Fintype ι] {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (C : Matrix (Fin d) ι R)
    (i : Fin d) (a : ι) : (M * C) i a = (M *ᵥ fun j => C j a) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mul_eq_of_cols {R ι : Type} [CommRing R] [Fintype ι] {d d₁ : ℕ} (K : Matrix (Fin d) (Fin d) R)
    (C : Matrix (Fin d) ι R) (C' : Matrix ι (Fin d) R) (hC : C * C' = 1) (I : Matrix (Fin d) (Fin d₁) R)
    (P : Matrix (Fin d₁) (Fin d) R) (hP : P * I = 1) (S : ι → Prop)
    (hS : ∀ a, S a → (P *ᵥ fun j => C j a) = 0)
    (hT : ∀ a, ¬ S a → (∃ z, (fun j => C j a) = I *ᵥ z) ∧ (K *ᵥ fun j => C j a) = fun j => C j a) : K * I = I := by
  classical
  have key : K * I * P * C = I * P * C := by
    ext i a
    rw [col_mul, col_mul]
    by_cases h : S a
    · simp only [← mulVec_mulVec, hS a h, mulVec_zero]
    · obtain ⟨⟨z, hz⟩, hK⟩ := hT a h
      have h1 : (I *ᵥ (P *ᵥ fun j => C j a)) = fun j => C j a := by
        rw [hz, show P *ᵥ (I *ᵥ z) = z by rw [mulVec_mulVec, hP, one_mulVec]]
      simp only [← mulVec_mulVec, h1, hK]
  have k2 : K * I * P = I * P := by
    calc K * I * P = K * I * P * C * C' := by rw [Matrix.mul_assoc (K * I * P) C C', hC, Matrix.mul_one]
      _ = I * P * C * C' := by rw [key]
      _ = I * P := by rw [Matrix.mul_assoc (I * P) C C', hC, Matrix.mul_one]
  calc K * I = K * I * P * I := by rw [Matrix.mul_assoc (K * I) P I, hP, Matrix.mul_one]
    _ = I * P * I := by rw [k2]
    _ = I := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_eq_of_piInf {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type}
    (A A' : Matrix m n (AE F E)) (hA : At (evI F) (A - A')) (h : ∀ w, A.map (piInf (τ w)) = A'.map (piInf (τ w))) :
    A = A' := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ (fun u hu => ?_) (fun w => ?_))
  · have := congrFun (congrFun (hA u hu) i) j
    simpa using this
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun (h w) i) j

theorem vec_eq_of_piInf {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : Type}
    (v v' : m → AE F E) (hA : At (evI F) (v - v')) (h : ∀ w i, piInf (τ w) (v i) = piInf (τ w) (v' i)) : v = v' := by
  funext i
  refine sub_eq_zero.1 (GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ _ (fun u hu => ?_) (fun w => ?_))
  · have := congrFun (hA u hu) i
    simpa using this
  · rw [map_sub, sub_eq_zero]
    exact h w i

end GlobalTheory.AdaptedFrameLevi

namespace GlobalTheory.AdaptedFrameLevi

open Matrix

theorem exists_isLevi_of_adaptedFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r s →
    W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix Rn Sn) ℂ),
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm Rn Sn) → GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ →
    ∀ (u : InfinitePlace F → ℂ), (∀ w, ‖u w‖ = 1) → ∀ k ∈ UAt σ W (evI F), (∀ w, (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = u w * C w i (.inl r₀)) ∧
        (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = u w * C w i (.inr s₀)) ∧
        ∀ c, c ≠ .inl r₀ → c ≠ .inr s₀ → ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i c = C w i c) →
      ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∀ w, piInf (B.emb w) (t : AE F E) = u w := by
  intro F E _ _ _ _ _ σ B d d₁ i₀ i₁ r s r₁ s₁ W W₁ H' hB hW hW₁ hA Rn Sn r₀ s₀ C hF hθC hAF u hu k hk hK
  have hCM := hB.cm
  have hu0 : ∀ w, u w ≠ 0 := fun w h => by
    have := hu w
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨t, ht, htw⟩ := GlobalTheory.ThK.exists_unit_at_evI_piInf_eq σ B.emb u hCM hu0
  obtain ⟨π, p1, -, -, p4, p5⟩ := GlobalTheory.LeviUnitary.exists_proj hB hW hW₁ hA
  have hkA : At (evI F) (mat k - 1) := hk
  have hKr : ∀ w, ((mat k).map (piInf (B.emb w)) *ᵥ fun j => C w j (.inl r₀)) = u w • fun j => C w j (.inl r₀) := by
    intro w
    funext i
    rw [← col_mul, (hK w).1 i]
    rfl
  have hKs : ∀ w, ((mat k).map (piInf (B.emb w)) *ᵥ fun j => C w j (.inr s₀)) = u w • fun j => C w j (.inr s₀) := by
    intro w
    funext i
    rw [← col_mul, (hK w).2.1 i]
    rfl
  have hKo : ∀ w a, a ≠ .inl r₀ → a ≠ .inr s₀ →
      ((mat k).map (piInf (B.emb w)) *ᵥ fun j => C w j a) = fun j => C w j a := by
    intro w a h1 h2
    funext i
    rw [← col_mul, (hK w).2.2 a h1 h2 i]
  have hKx : ∀ w, ((mat k).map (piInf (B.emb w)) *ᵥ fun i => (B.emb w).1 (H'.x i)) =
      u w • fun i => (B.emb w).1 (H'.x i) := by
    intro w
    obtain ⟨c, -, hc⟩ := (hAF w).1
    have e : (fun i => (B.emb w).1 (H'.x i)) = c • ((fun j => C w j (.inl r₀)) + fun j => C w j (.inr s₀)) :=
      funext fun i => by simp [hc i]
    rw [e, mulVec_smul, mulVec_add, hKr, hKs, ← smul_add, smul_comm]
  have hKy : ∀ w, ((mat k).map (piInf (B.emb w)) *ᵥ fun i => (B.emb w).1 (H'.y i)) =
      u w • fun i => (B.emb w).1 (H'.y i) := by
    intro w
    obtain ⟨c₁, c₂, hc⟩ := (hAF w).2.1
    have e : (fun i => (B.emb w).1 (H'.y i)) = c₁ • (fun j => C w j (.inl r₀)) + c₂ • fun j => C w j (.inr s₀) :=
      funext fun i => by simp [hc i]
    rw [e, mulVec_add, mulVec_smul, mulVec_smul, hKr, hKs, smul_add, smul_comm c₁, smul_comm c₂]
  have hKι : ∀ w, (mat k).map (piInf (B.emb w)) * H'.ι.map (B.emb w).1 = H'.ι.map (B.emb w).1 := by
    intro w
    obtain ⟨C', hC'⟩ := (hF w).2
    have hP : π.map (B.emb w).1 * H'.ι.map (B.emb w).1 = 1 := by
      rw [← Matrix.map_mul, p1, Matrix.map_one _ (map_zero _) (map_one _)]
    have hPx := GlobalTheory.LeviKInf.map_mulVec_zero (B.emb w).1 π _ p4
    have hPy := GlobalTheory.LeviKInf.map_mulVec_zero (B.emb w).1 π _ p5
    obtain ⟨c, hc0, hc⟩ := (hAF w).1
    obtain ⟨-, c', hc'0, hy⟩ := hA.cartan w
    have hθr : (W.θ w *ᵥ fun j => C w j (.inl r₀)) = fun j => C w j (.inl r₀) := by
      funext i
      rw [← col_mul, hθC w]
      simp [Matrix.mul_apply, Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply]
    have hθs : (W.θ w *ᵥ fun j => C w j (.inr s₀)) = -fun j => C w j (.inr s₀) := by
      funext i
      rw [← col_mul, hθC w]
      simp [Matrix.mul_apply, Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply]
    have hx : (fun i => (B.emb w).1 (H'.x i)) = c • ((fun j => C w j (.inl r₀)) + fun j => C w j (.inr s₀)) :=
      funext fun i => by simp [hc i]
    rw [hx, mulVec_smul, mulVec_add] at hPx
    rw [hy, hx, mulVec_smul, mulVec_smul, mulVec_add, hθr, hθs, mulVec_smul, mulVec_add, mulVec_neg] at hPy
    have e1 := (smul_eq_zero.1 hPx).resolve_left hc0
    have e2 := (smul_eq_zero.1 ((smul_eq_zero.1 hPy).resolve_left hc'0)).resolve_left hc0
    have hr0 : (π.map (B.emb w).1 *ᵥ fun j => C w j (.inl r₀)) = 0 := funext fun j => by
      have a := congrFun e1 j
      have b := congrFun e2 j
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at a b
      simp only [Pi.zero_apply]
      linear_combination (a + b) / 2
    have hs0 : (π.map (B.emb w).1 *ᵥ fun j => C w j (.inr s₀)) = 0 := funext fun j => by
      have a := congrFun e1 j
      have b := congrFun e2 j
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at a b
      simp only [Pi.zero_apply]
      linear_combination (a - b) / 2
    refine mul_eq_of_cols _ (C w) C' hC' _ _ hP (fun a => a = .inl r₀ ∨ a = .inr s₀) ?_ ?_
    · rintro a (rfl | rfl)
      exacts [hr0, hs0]
    · intro a ha
      have h1 : a ≠ .inl r₀ := fun h => ha (Or.inl h)
      have h2 : a ≠ .inr s₀ := fun h => ha (Or.inr h)
      obtain ⟨z, hz⟩ := (hAF w).2.2 a h1 h2
      exact ⟨⟨z, funext hz⟩, hKo w a h1 h2⟩
  have hv : ∀ w (x : Fin d → E), (piInf (B.emb w)) ∘ incV F x = fun i => (B.emb w).1 (x i) :=
    fun w x => funext fun i => GlobalTheory.IwaAdelicIso.piInf_inclR _ _
  have hti : At (evI F) (((t⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun a ha => by
    have e : ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((t⁻¹ : (AE F E)ˣ) : AE F E) * ((t : AE F E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, ht a ha, mul_zero, neg_zero]
  have hcA : At (evI F) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun a ha => by
    rw [← map_one (cA σ), ← map_sub, ← map_smul, hti a ha, map_zero]
  have hstar : ∀ w, piInf (B.emb w) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) = u w := by
    intro w
    have h1 : piInf (B.emb w) ((t⁻¹ : (AE F E)ˣ) : AE F E) = (u w)⁻¹ := by
      have := congrArg (piInf (B.emb w)) (Units.inv_mul t)
      rw [map_mul, map_one, htw] at this
      exact eq_inv_of_mul_eq_one_left this
    have h2 : star (u w) = (u w)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu w]
      simp
    rw [GlobalTheory.RealLift.KLineProof.piInf_cA hCM, h1, ← h2, star_star]
  refine ⟨t, ⟨?_, ?_, ?_⟩, htw⟩
  · apply vec_eq_of_piInf hCM B.emb
    · intro a ha
      have e : mat k *ᵥ incV F H'.x - t.1 • incV F H'.x = (mat k - 1) *ᵥ incV F H'.x - (t.1 - 1) • incV F H'.x := by
        rw [sub_mulVec, one_mulVec, sub_smul, one_smul]
        abel
      rw [e, smul_sub, ← Matrix.smul_mulVec, hkA a ha, zero_mulVec, ← smul_assoc, ht a ha, zero_smul, sub_zero]
    · intro w i
      rw [RingHom.map_mulVec, hv, hKx w, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, htw]
      simp [incV, GlobalTheory.IwaAdelicIso.piInf_inclR]
  · apply vec_eq_of_piInf hCM B.emb
    · intro a ha
      have e : mat k *ᵥ incV F H'.y - cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) • incV F H'.y =
          (mat k - 1) *ᵥ incV F H'.y - (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1) • incV F H'.y := by
        rw [sub_mulVec, one_mulVec, sub_smul, one_smul]
        abel
      rw [e, smul_sub, ← Matrix.smul_mulVec, hkA a ha, zero_mulVec, ← smul_assoc, hcA a ha, zero_smul, sub_zero]
    · intro w i
      rw [RingHom.map_mulVec, hv, hKy w, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hstar]
      simp [incV, GlobalTheory.IwaAdelicIso.piInf_inclR]
  · have h1 : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [h1, Matrix.mul_one]
    apply mat_eq_of_piInf hCM B.emb
    · intro a ha
      rw [show mat k * incM F H'.ι - incM F H'.ι = (mat k - 1) * incM F H'.ι by rw [Matrix.sub_mul, Matrix.one_mul],
        ← Matrix.smul_mul, hkA a ha, Matrix.zero_mul]
    · intro w
      rw [Matrix.map_mul, GlobalTheory.LeviKInf.incM_map_piInf]
      exact hKι w

end GlobalTheory.AdaptedFrameLevi

end
