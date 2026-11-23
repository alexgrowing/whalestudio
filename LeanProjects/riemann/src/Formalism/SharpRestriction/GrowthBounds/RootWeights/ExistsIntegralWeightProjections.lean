import Formalism.SharpRestriction.GrowthBounds.RootWeights.GlOperatorMemIntegralEnveloping

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem findim_exists_finite_weights [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) :
    ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu := by
  have hc := (Submodule.fg_iff_compact (⊤ : Submodule (KK O) V)).1 Module.Finite.fg_top
  first
  | exact IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge
  | exact IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge

theorem linear_map_ext_on_weights {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {W : Type*} [AddCommGroup W] [Module (KK O) W]
    {A B : V →ₗ[KK O] W} (h : ∀ nu ∈ F, ∀ x ∈ weightSp E nu, A x = B x) : A = B := by
  have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (A - B) := by
    refine iSup₂_le fun nu hnu x hx => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h nu hnu x hx
  ext x
  have hx : x ∈ LinearMap.ker (A - B) := hle (hF (Submodule.mem_top : x ∈ (⊤ : Submodule (KK O) V)))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
  exact hx

theorem exists_integral_weight_projection [CharZero (KK O)] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (F : Finset (Fin n → ℤ)) :
    ∃ (P : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧ (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧
      (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P x ∈ M := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, fun _ => 1, rfl, by simp, by simp, fun M _ x hx => by simpa using hx⟩
  | insert nu0 F _ ih =>
    obtain ⟨P, g, g1, g0, hP, hPM⟩ := ih
    by_cases h : nu0 = mu
    · refine ⟨P, g, g1, ?_, hP, hPM⟩
      intro nu hnu hne
      rcases mem_insert.1 hnu with rfl | h2
      · exact absurd h hne
      · exact g0 nu h2 hne
    · obtain ⟨T, g', g'1, g'0, hT, hTM⟩ := lattice_stable_weight_separator (O := O) E h
      refine ⟨T * P, fun nu => g' nu * g nu, by simp [g1, g'1], ?_, ?_, ?_⟩
      · intro nu hnu hne
        rcases mem_insert.1 hnu with rfl | h2
        · simp [g'0]
        · simp [g0 nu h2 hne]
      · intro nu x hx
        rw [Module.End.mul_apply, hP nu x hx, map_smul, hT nu x hx, smul_smul]
        push_cast
        rw [mul_comm]
      · intro M hM x hx
        exact hTM M hM _ (hPM M hM x hx)

theorem exists_integral_weight_projections [CharZero (KK O)] (E : GLOps n (KK O) V) (F : Finset (Fin n → ℤ)) :
    ∃ P : (Fin n → ℤ) → Module.End (KK O) V,
      (∀ mu, ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P mu x ∈ M) ∧
      (∀ mu, ∀ x ∈ weightSp E mu, P mu x = x) ∧
      (∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) := by
  choose P g hg1 hg0 hgw hgM using fun mu => exists_integral_weight_projection E mu F
  refine ⟨P, fun mu M hM x hx => hgM mu M hM x hx, fun mu x hx => ?_, fun mu nu hnu hne x hx => ?_⟩
  · rw [hgw mu mu x hx, hg1 mu]
    simp
  · rw [hgw mu nu x hx, hg0 mu nu hnu hne]
    simp

theorem sum_weight_projections_eq_one {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) : ∑ mu ∈ F, P mu = 1 := by
  refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single nu (fun mu _ hne => h0 mu nu hnu (Ne.symm hne) x hx)
    (fun h => absurd hnu h)]
  rw [h1 nu x hx]
  rfl

private theorem end_mul_apply' (f g : Module.End (KK O) V) (x : V) : (f * g) x = f (g x) := rfl

private theorem diagonal_apply_of_mem_weightSp {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) : E a a x = ((mu a : ℤ) : KK O) • x := by
  rw [weightSp, Submodule.mem_iInf] at hx
  have h := LinearMap.mem_ker.1 (hx a)
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply] at h
  exact h

theorem diagonal_weight_projection_comm {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu : Fin n → ℤ) (a : Fin n) :
    E a a * P mu = (mu a : KK O) • P mu ∧ P mu * E a a = (mu a : KK O) • P mu := by
  constructor
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    by_cases h : nu = mu
    · subst h
      rw [end_mul_apply', LinearMap.smul_apply, h1 _ x hx]
      exact diagonal_apply_of_mem_weightSp hx a
    · rw [end_mul_apply', LinearMap.smul_apply, h0 mu nu hnu h x hx, map_zero, smul_zero]
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    rw [end_mul_apply', LinearMap.smul_apply, diagonal_apply_of_mem_weightSp hx a, map_smul]
    by_cases h : nu = mu
    · subst h
      rw [h1 _ x hx]
    · rw [h0 mu nu hnu h x hx, smul_zero, smul_zero]

def adjointEndAction (E : GLOps n (KK O) V) : GLOps n (KK O) (Module.End (KK O) V) :=
  fun a b => LinearMap.mulLeft (KK O) (E a b) - LinearMap.mulRight (KK O) (E a b)

theorem adjointEndAction_apply (E : GLOps n (KK O) V) (a b : Fin n) (f : Module.End (KK O) V) :
    adjointEndAction E a b f = E a b * f - f * E a b := by
  first
  | rfl
  | simp [adjointEndAction]

private theorem end_one_apply {W : Type*} [AddCommGroup W] [Module (KK O) W] (x : W) :
    (1 : Module.End (KK O) W) x = x := rfl

theorem weight_block_adjoint_weight {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu nu : Fin n → ℤ)
    (f : Module.End (KK O) V) : P mu * f * P nu ∈ weightSp (adjointEndAction E) (mu - nu) := by
  rw [weightSp, Submodule.mem_iInf]
  intro a
  obtain ⟨hm, -⟩ := diagonal_weight_projection_comm hF h1 h0 mu a
  obtain ⟨-, hn⟩ := diagonal_weight_projection_comm hF h1 h0 nu a
  have e1 : E a a * (P mu * f * P nu) = ((mu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [← mul_assoc, ← mul_assoc, hm, smul_mul_assoc, smul_mul_assoc]
  have e2 : P mu * f * P nu * E a a = ((nu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [mul_assoc, hn, mul_smul_comm]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, adjointEndAction_apply, LinearMap.smul_apply, end_one_apply,
    e1, e2, Pi.sub_apply, Int.cast_sub, sub_smul]

theorem endomorphism_sum_weight_blocks {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (f : Module.End (KK O) V) :
    f = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
  have hs := sum_weight_projections_eq_one hF h1 h0
  calc f = (∑ mu ∈ F, P mu) * f * (∑ nu ∈ F, P nu) := by rw [hs, one_mul, mul_one]
    _ = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem adjoint_end_isGLRep [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E) :
    IsGLRep (adjointEndAction E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun f => ?_
    have hr := hE.1 a b c d
    have key : (adjointEndAction E a b * adjointEndAction E c d - adjointEndAction E c d * adjointEndAction E a b) f =
        (E a b * E c d - E c d * E a b) * f - f * (E a b * E c d - E c d * E a b) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, adjointEndAction_apply]
      noncomm_ring
    rw [key, hr]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, adjointEndAction_apply] <;> noncomm_ring
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
    obtain ⟨P, -, h1, h0⟩ := exists_integral_weight_projections (O := O) E F
    rw [eq_top_iff]
    intro f _
    rw [endomorphism_sum_weight_blocks hF h1 h0 f]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun nu _ => ?_
    exact Submodule.mem_iSup_of_mem (mu - nu) (weight_block_adjoint_weight hF h1 h0 mu nu f)

end hw

end Formalism.MainNotions.G.GLWeightTheory
