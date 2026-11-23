import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT bc)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure IsAdapted (X Y : Matrix (Fin n) (Fin r) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) : Prop where
  lat : Submodule.IsLattice E L
  dual : ∀ v, IsSelfDualAt σ J L v
  split : ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L
  maj : IsMajorantFrame σ J a
  cartan : ∀ w : InfinitePlace F, ∃ c : Fin r → w.Completion ⊗[F] E,
    cT (sigR _ σ) (bc (compInf F E w) a⁻¹).1 * (bc (compInf F E w) a⁻¹).1 * X.map (inclR (F := F) w.Completion) =
      (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) * diagonal c

def IsModerateForm (μ : (GAd σ J → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ (S : List (List (ℝ → GAd σ J))) (C : ℝ), (∀ l ∈ S, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSmoothModerate σ J f →
      (∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ B : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ B * (height σ J g : ℝ) ^ N) →
      (∀ l ∈ S, ∀ g, ‖l.foldr lineDer f g‖ ≤ (height σ J g : ℝ) ^ N) → ‖μ f‖ ≤ C

theorem isModerateForm_proj (g : GAd σ J) : IsModerateForm σ J (LinearMap.proj g) := fun N =>
  ⟨[[]], (height σ J g : ℝ) ^ N, by simp, fun _ _ _ h => h [] (by simp) g⟩

theorem exists_isAdapted_plane : ∃ L a,
    IsAdapted σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) !![0; 1] L a := by
  let b : GL (Fin 2) E := ⟨!![1, 1; 2⁻¹, -2⁻¹], !![2⁻¹, 1; 2⁻¹, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num⟩
  have h0 : ∀ (w : InfinitePlace F) (u : GL (Fin 2) E), (bc (compInf F E w) (bc (inclR (F := F) (AF F)) u)).1 =
      u.1.map (inclR (F := F) w.Completion) := fun w u => Matrix.ext fun i j => by
    change evInf F w 1 ⊗ₜ[F] _ = 1 ⊗ₜ[F] _
    rw [map_one]; rfl
  have h1 : ∀ (w : InfinitePlace F) (M : Matrix (Fin 2) (Fin 2) E),
      cT (sigR _ σ) (M.map (inclR (F := F) w.Completion)) = (cT (σ : E →+* E) M).map (inclR (F := F) w.Completion) :=
    fun w M => rfl
  refine ⟨stdLattice E 2, bc (inclR (F := F) (AF F)) b, isLattice_stdLattice, fun v => ?_, fun z hz i => ?_,
    fun w => ⟨![true, false], ?_⟩, fun w => ⟨fun _ => inclR (F := F) w.Completion 2⁻¹, ?_⟩⟩
  · have e : ∀ y x : Fin 2 → Fv F v ⊗[F] E,
        hLin σ !![0, 1; 1, 0] (Fv F v) y x = sigR _ σ (x 0) * y 1 + sigR _ σ (x 1) * y 0 := fun y x => by
      simp [hLin, hR, Formalism.UG.hform, JR, Fin.sum_univ_two]
    ext y
    rw [mem_latLoc_stdLattice]
    refine ⟨fun hy x hx => ?_, fun hy => Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · rw [e]
      exact add_mem (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 0)) (hy 1))
        (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 1)) (hy 0))
    · simpa [e] using hy ![0, 1] (mem_latLoc_stdLattice.2 (Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩))
    · simpa [e] using hy ![1, 0] (mem_latLoc_stdLattice.2 (Fin.forall_fin_two.2 ⟨one_mem _, zero_mem _⟩))
  · constructor <;> intro j _ <;> fin_cases j
    · simpa [cT, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] using hz 0 trivial
    · simp
    · simp
    · simpa [cT, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] using hz 1 trivial
  · rw [h0, h1, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    have : cT (σ : E →+* E) b.1 * !![0, 1; 1, 0] * b.1 = diagonal fun i => if ![true, false] i then 1 else -1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [b, cT, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> norm_num
    rw [this, diagonal_map (map_zero _)]
    exact congrArg diagonal (funext fun i => by split_ifs <;> simp)
  · have : cT (σ : E →+* E) (b⁻¹).1 * (b⁻¹).1 * (!![1; 0] : Matrix (Fin 2) (Fin 1) E) =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) * (!![0; 1] : Matrix (Fin 2) (Fin 1) E) * diagonal fun _ : Fin 1 => (2⁻¹ : E) := by
      ext i j; rw [mul_diagonal]; fin_cases i <;> fin_cases j <;> simp [b, cT, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> norm_num
    rw [← map_inv, h0, h1, JR, ← Matrix.map_mul, ← Matrix.map_mul, this]
    exact Matrix.map_mul.trans (congrArg₂ (· * ·) Matrix.map_mul (diagonal_map (map_zero _)))

end GlobalTheory.EisLine

namespace GlobalTheory.Published

open GlobalTheory.EisLine in

def EisensteinIsotropicLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x y : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → y = Y.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
        (∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
          ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
            HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)) ∧
        (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
          ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
            IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
            ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
              Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
              ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
                c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
        MeromorphicOn c Set.univ ∧
        (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
        ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

end GlobalTheory.Published

end
