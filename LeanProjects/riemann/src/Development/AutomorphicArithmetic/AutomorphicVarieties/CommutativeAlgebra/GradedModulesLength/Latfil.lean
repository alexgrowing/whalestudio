import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Satfil

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A E τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing E] [Algebra O E]
  (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ E)

private theorem mem_fil_zero (g : MvPowerSeries τ E) : g ∈ fil E wt 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

private theorem fil_mul {a b : ℕ} {g h : MvPowerSeries τ E} (hg : g ∈ fil E wt a) (hh : h ∈ fil E wt b) :
    g * h ∈ fil E wt (a + b) := (fil_holds E τ wt a b g h hg hh).1

private theorem fil_of_wt {j : ℤ} {g : MvPowerSeries τ E} (hg : g ∈ wtPart E wt j) : g ∈ fil E wt (-j).toNat :=
  (fil_holds E τ wt 0 0 g g (mem_fil_zero wt g) (mem_fil_zero wt g)).2 j hg

private def sf (j : ℤ) (n : ℕ) : Submodule (𝒜 0) A where
  carrier := {f | f ∈ 𝒜 j ∧ φ f ∈ fil E wt n}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2 hg.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  smul_mem' c f hf := by
    refine ⟨(oz 𝒜 j).smul_mem c hf.1, ?_⟩
    show φ ((c : A) * f) ∈ fil E wt n
    have := fil_mul wt (mem_fil_zero wt (φ (c : A))) hf.2
    rwa [zero_add, ← map_mul] at this

private theorem sf_mul {j j' : ℤ} {n n' : ℕ} {M M' : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n)
    (h' : M' ≤ sf 𝒜 wt φ j' n') : M * M' ≤ sf 𝒜 wt φ (j + j') (n + n') := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := h ha
  obtain ⟨hb1, hb2⟩ := h' hb
  refine ⟨SetLike.GradedMul.mul_mem ha1 hb1, ?_⟩
  rw [map_mul]
  exact fil_mul wt ha2 hb2

private theorem sf_pow {j : ℤ} {n : ℕ} {M : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n) (k : ℕ) :
    M ^ k ≤ sf 𝒜 wt φ (k * j) (k * n) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    rw [Submodule.one_le]
    refine ⟨SetLike.GradedOne.one_mem, ?_⟩
    exact mem_fil_zero wt _
  | succ k ih =>
    have := sf_mul 𝒜 wt φ ih h
    rw [pow_succ]
    convert this using 2 <;> push_cast <;> ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.latfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    ∀ F ∈ 𝒜 (-1), F ∈ satSq x → ∀ (μ : Fin 3 →₀ ℕ) (f : A), f ∈ lat (mN 𝒜 F) μ →
      f ∈ 𝒜 (2 * ((μ 1 : ℤ) - μ 0 - μ 2)) ∧ φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW τ _ wt φ hφ F hF hFs μ f hf
  have h0 : oz 𝒜 (-2) ≤ sf 𝒜 wt φ (-2) 2 := fun g hg => ⟨hg, fil_of_wt wt (hφ.graded (-2) g hg)⟩
  have h1 : oz 𝒜 2 ≤ sf 𝒜 wt φ 2 0 := fun g hg => ⟨hg, mem_fil_zero wt _⟩
  have hF2 : φ F ∈ fil (FractionRing O) wt 2 := (satfil_holds O A 𝒜 x hW τ wt φ hφ).1 F hF hFs
  have h2 : Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ sf 𝒜 wt φ (-2) 4 := by
    refine sup_le ?_ (sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ h0 h0) h1)
    rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨sq_mem_neg 𝒜 hF, ?_⟩
    rw [sq, map_mul]
    exact fil_mul wt hF2 hF2
  rw [lat, Fin.prod_univ_three] at hf
  have key := sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ (sf_pow 𝒜 wt φ h0 (μ 0)) (sf_pow 𝒜 wt φ h1 (μ 1)))
    (sf_pow 𝒜 wt φ h2 (μ 2)) hf
  have e1 : 2 * ((μ 1 : ℤ) - μ 0 - μ 2) = μ 0 * (-2) + μ 1 * 2 + μ 2 * (-2) := by ring
  have e2 : 2 * μ 0 + 4 * μ 2 = μ 0 * 2 + μ 1 * 0 + μ 2 * 4 := by ring
  rw [e1, e2]
  exact key
