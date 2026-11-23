import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviKCentre

open Matrix

theorem theta_cols {d R S : ℕ} (θ : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ)
    (h : θ * C = C * Formalism.BasicNotions.TH.Jm R S) (r₀ : Fin R) (s₀ : Fin S) :
    θ *ᵥ (fun i => C i (.inl r₀)) = (fun i => C i (.inl r₀)) ∧ θ *ᵥ (fun i => C i (.inr s₀)) = -(fun i => C i (.inr s₀)) := by
  constructor
  · funext i
    have := congrFun (congrFun h i) (.inl r₀)
    simpa [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.one_apply] using this
  · funext i
    have := congrFun (congrFun h i) (.inr s₀)
    simpa [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.one_apply] using this

theorem cols_eigen {d R S : ℕ} (K θ : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ)
    (h : θ * C = C * Formalism.BasicNotions.TH.Jm R S) (hc : Commute K θ) (r₀ : Fin R) (s₀ : Fin S) {a t : ℂ} (ha : a ≠ 0)
    (X : Fin d → ℂ) (hX : ∀ i, X i = a * (C i (.inl r₀) + C i (.inr s₀))) (hKX : K *ᵥ X = t • X) :
    (∀ i, (K * C) i (.inl r₀) = t * C i (.inl r₀)) ∧ (∀ i, (K * C) i (.inr s₀) = t * C i (.inr s₀)) := by
  obtain ⟨hr, hs⟩ := theta_cols θ C h r₀ s₀
  set u : Fin d → ℂ := fun i => C i (.inl r₀) with hu
  set v : Fin d → ℂ := fun i => C i (.inr s₀) with hv
  have hX' : X = a • (u + v) := funext fun i => by simp [hX, hu, hv]
  have hθX : θ *ᵥ X = a • (u - v) := by
    rw [hX', mulVec_smul, mulVec_add, hr, hs, sub_eq_add_neg]
  have hKθX : K *ᵥ (θ *ᵥ X) = t • (θ *ᵥ X) := by
    rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, hKX, mulVec_smul]
  rw [hθX, mulVec_smul, smul_comm] at hKθX
  rw [hX', mulVec_smul, smul_comm] at hKX
  have e1 := smul_right_injective _ ha hKX
  have e2 := smul_right_injective _ ha hKθX
  have hcol : ∀ c i, (K * C) i c = (K *ᵥ fun j => C j c) i := fun c i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have f1 := congrFun e1 i
    have f2 := congrFun e2 i
    simp only [mulVec_add, mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f1 f2
    rw [hcol]
    change (K *ᵥ u) i = t * u i
    linear_combination (f1 + f2) / 2
  · have f1 := congrFun e1 i
    have f2 := congrFun e2 i
    simp only [mulVec_add, mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f1 f2
    rw [hcol]
    change (K *ᵥ v) i = t * v i
    linear_combination (f1 - f2) / 2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_eigen {w : InfinitePlace F} (τ : EmbOver E w) {d : ℕ} (M : Matrix (Fin d) (Fin d) (AE F E)) (v : Fin d → E)
    (a : AE F E) (h : M *ᵥ incV F v = a • incV F v) :
    M.map (piInf τ) *ᵥ (fun i => τ.1 (v i)) = piInf τ a • fun i => τ.1 (v i) := by
  have hinc : ∀ e : E, piInf τ (inclR (F := F) (AF F) e) = τ.1 e := fun e => by
    simp [piInf, inclR, compInf, infEmb_tmul]
  funext i
  have h1 := congrArg (fun z => piInf τ (z i)) h
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h1
  have e3 : (piInf τ) ∘ incV F v = fun i => τ.1 (v i) := funext fun j => hinc _
  rw [e3] at h1
  simpa [incV, hinc] using h1

end GlobalTheory.LeviKCentre

namespace GlobalTheory.LeviKCentre

open Matrix

theorem levi_one_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r s →
    W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix Rn Sn) ℂ),
    (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm Rn Sn) → GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ →
    ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k →
      At (evI F) ((t : AE F E) - 1) ∧ (absE F E t : ℝ) = 1 ∧ ∀ w, ‖piInf (B.emb w) (t : AE F E)‖ = 1 ∧
        (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = piInf (B.emb w) (t : AE F E) * C w i (.inl r₀)) ∧
        (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = piInf (B.emb w) (t : AE F E) * C w i (.inr s₀)) ∧
        ∀ c, c ≠ .inl r₀ → c ≠ .inr s₀ → ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i c = C w i c := by
  intro F E _ _ _ _ _ σ B d d₁ i₀ i₁ r s r₁ s₁ W W₁ H' hB hW hW₁ hA Rn Sn r₀ s₀ C _hCf hθC hAF k hk t hL
  have hcm := hB.cm
  obtain ⟨hLx, hLy, hLι⟩ := hL
  have hx0 : H'.x ≠ 0 := fun h => by have := hA.xy; simp [form, h] at this
  have hy0 : H'.y ≠ 0 := fun h => by have := hA.xy; simp [form, h, Matrix.mulVec, dotProduct] at this
  obtain ⟨i, hi⟩ : ∃ i, H'.x i ≠ 0 := by by_contra hc; push_neg at hc; exact hx0 (funext hc)
  have hAt : At (evI F) ((t : AE F E) - 1) := by
    intro u hu
    have h1 : (u • (mat k - 1)) *ᵥ incV F H'.x = 0 := by rw [hk.1 u hu, zero_mulVec]
    rw [Matrix.smul_mulVec, sub_mulVec, one_mulVec, hLx] at h1
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, incV] at h2
    have hu' : (u • ((t : AE F E) - 1)) * inclR (F := F) (AF F) (H'.x i) = 0 := by
      rw [smul_mul_assoc, sub_mul, one_mul]; exact h2
    have hunit : inclR (F := F) (AF F) (H'.x i) * inclR (F := F) (AF F) (H'.x i)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    calc u • ((t : AE F E) - 1) = (u • ((t : AE F E) - 1)) * inclR (F := F) (AF F) (H'.x i) *
          inclR (F := F) (AF F) (H'.x i)⁻¹ := by rw [mul_assoc, hunit, mul_one]
      _ = 0 := by rw [hu', zero_mul]
  have hplace : ∀ w, ‖piInf (B.emb w) (t : AE F E)‖ = 1 ∧
      (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = piInf (B.emb w) (t : AE F E) * C w i (.inl r₀)) ∧
      (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = piInf (B.emb w) (t : AE F E) * C w i (.inr s₀)) ∧
      ∀ c, c ≠ .inl r₀ → c ≠ .inr s₀ → ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i c = C w i c := by
    intro w
    have hinc : ∀ e : E, piInf (B.emb w) (inclR (F := F) (AF F) e) = (B.emb w).1 e := fun e => by
      simp [piInf, inclR, compInf, infEmb_tmul]
    have hX := map_eigen (B.emb w) (mat k) H'.x _ hLx
    have hY := map_eigen (B.emb w) (mat k) H'.y _ hLy
    rw [GlobalTheory.RealLift.KLineProof.piInf_cA hcm] at hY
    obtain ⟨hθι, c, hc, hyθ⟩ := hA.cartan w
    have hcomm := hk.2 w
    have hKY : (mat k).map (piInf (B.emb w)) *ᵥ (fun i => (B.emb w).1 (H'.y i)) =
        piInf (B.emb w) (t : AE F E) • (fun i => (B.emb w).1 (H'.y i)) := by
      rw [hyθ, mulVec_smul, mulVec_mulVec, hcomm.eq, ← mulVec_mulVec, hX, mulVec_smul, smul_comm]
    have hYne : (fun i => (B.emb w).1 (H'.y i)) ≠ 0 := fun h =>
      hy0 (funext fun i => (B.emb w).1.injective (by simpa using congrFun h i))
    obtain ⟨j, hj⟩ : ∃ j, (B.emb w).1 (H'.y j) ≠ 0 := by
      by_contra hc'; push_neg at hc'; exact hYne (funext hc')
    have heq : piInf (B.emb w) (t : AE F E) = star (piInf (B.emb w) ((t⁻¹ : (AE F E)ˣ) : AE F E)) := by
      have := congrFun (hKY.symm.trans hY) j
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
    have hprod : piInf (B.emb w) (t : AE F E) * piInf (B.emb w) ((t⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hn : piInf (B.emb w) (t : AE F E) * star (piInf (B.emb w) (t : AE F E)) = 1 := by
      have := congrArg star hprod
      rw [star_mul', star_one, ← heq] at this
      rw [mul_comm]; exact this
    have hn2 : ‖piInf (B.emb w) (t : AE F E)‖ ^ 2 = 1 := by
      have := Complex.mul_conj' (piInf (B.emb w) (t : AE F E))
      rw [show (starRingEnd ℂ) (piInf (B.emb w) (t : AE F E)) = star (piInf (B.emb w) (t : AE F E)) from rfl, hn] at this
      exact_mod_cast this.symm
    have hnorm := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hn2
    obtain ⟨⟨a, ha, hax⟩, -, hoth⟩ := hAF w
    obtain ⟨h1, h2⟩ := cols_eigen _ _ (C w) (hθC w) hcomm r₀ s₀ ha _ hax hX
    refine ⟨hnorm, h1, h2, fun cc hc1 hc2 i => ?_⟩
    obtain ⟨z, hz⟩ := hoth cc hc1 hc2
    have hm1 : mat (1 : UA σ W₁.J) = 1 := rfl
    have hKι : (mat k).map (piInf (B.emb w)) * H'.ι.map (B.emb w).1 = H'.ι.map (B.emb w).1 := by
      have e := congrArg (fun A => A.map (piInf (B.emb w))) hLι
      have e2 : (incM F H'.ι).map (piInf (B.emb w)) = H'.ι.map (B.emb w).1 := by
        ext a b; simp [incM, hinc]
      simp only [Matrix.map_mul, hm1, Matrix.mul_one, e2] at e
      exact e
    have hcol : (fun j => C w j cc) = H'.ι.map (B.emb w).1 *ᵥ z := funext hz
    have e3 : ((mat k).map (piInf (B.emb w)) * C w) i cc = ((mat k).map (piInf (B.emb w)) *ᵥ (fun j => C w j cc)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e3, hcol, mulVec_mulVec, hKι]
    exact (hz i).symm
  have habs : absE F E t = 1 := by
    rw [GlobalTheory.Doubling.absE_apply]
    have hf : ∀ v, GlobalTheory.Doubling.unitFin F E v t = 1 := fun v => Units.ext (by
      have := (at_evI_iff.1 hAt) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this)
    simp only [hf, map_one, finprod_one, mul_one]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_eq_sq hcm (B.emb w)]
    change ‖piInf (B.emb w) t.1‖₊ ^ 2 = 1
    have := (hplace w).1
    rw [show ‖piInf (B.emb w) t.1‖₊ = 1 from NNReal.eq (by simpa using this), one_pow]
  exact ⟨hAt, by rw [habs]; rfl, hplace⟩

end GlobalTheory.LeviKCentre
