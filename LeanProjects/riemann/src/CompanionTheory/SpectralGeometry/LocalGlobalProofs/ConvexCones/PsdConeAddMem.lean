import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Orth

variable {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

def orthSum (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ) :
    (X₁ × X₂) →ₗ[ℤ] (X₁ × X₂) →ₗ[ℤ] ℝ :=
  B₁.compl₁₂ (LinearMap.fst ℤ X₁ X₂) (LinearMap.fst ℤ X₁ X₂) +
    B₂.compl₁₂ (LinearMap.snd ℤ X₁ X₂) (LinearMap.snd ℤ X₁ X₂)

@[simp] theorem orthSum_apply (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ) (u v : X₁ × X₂) :
    orthSum B₁ B₂ u v = B₁ u.1 v.1 + B₂ u.2 v.2 := rfl

theorem sum_basis_nonneg {K : Type} [Fintype K] (e : Module.Basis K ℤ X₁) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B)
    (c : K → ℝ) : 0 ≤ ∑ k, ∑ l, c k * c l * B (e k) (e l) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact ((isPosDef_iff_basis e B).1 h c hc).le

theorem isPosDef_orthSum {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (e₁ : Module.Basis K₁ ℤ X₁)
    (e₂ : Module.Basis K₂ ℤ X₂) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ}
    (h₁ : IsPosDef B₁) (h₂ : IsPosDef B₂) : IsPosDef (orthSum B₁ B₂) := by
  rw [isPosDef_iff_basis (e₁.prod e₂)]
  intro c hc
  have key : ∑ i, ∑ j, c i * c j * orthSum B₁ B₂ ((e₁.prod e₂) i) ((e₁.prod e₂) j) =
      (∑ k, ∑ l, c (Sum.inl k) * c (Sum.inl l) * B₁ (e₁ k) (e₁ l)) +
        ∑ k, ∑ l, c (Sum.inr k) * c (Sum.inr l) * B₂ (e₂ k) (e₂ l) := by
    simp [Fintype.sum_sum_type, Finset.sum_add_distrib]
  rw [key]
  by_cases h0 : (fun k => c (Sum.inl k)) = 0
  · have h3 : (fun k => c (Sum.inr k)) ≠ 0 := fun h3 => hc (by
      ext (k | k)
      · exact congrFun h0 k
      · exact congrFun h3 k)
    exact add_pos_of_nonneg_of_pos (sum_basis_nonneg e₁ h₁ _) ((isPosDef_iff_basis e₂ B₂).1 h₂ _ h3)
  · exact add_pos_of_pos_of_nonneg ((isPosDef_iff_basis e₁ B₁).1 h₁ _ h0) (sum_basis_nonneg e₂ h₂ _)

theorem isPosDef_compl_injective {Y : Type} [AddCommGroup Y] {C : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef C)
    (j : Y →ₗ[ℤ] X₁) (hj : Function.Injective j) : IsPosDef (C.compl₁₂ j j) := fun n x hx c hc => by
  simpa using h n (fun i => j (x i)) (hx.map' j (LinearMap.ker_eq_bot.2 hj)) c hc

end Orth

section DedekindLFunctions

variable (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]

theorem free_int_of_torsion_eq_bot (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (ht : Submodule.torsion O M = ⊥) : Module.Free ℤ M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  have : IsAddTorsionFree M := by
    refine ⟨fun n hn a b hab => ?_⟩
    have h0 : ((n : ℕ) : O) ≠ 0 := by exact_mod_cast hn
    have h1 : ((n : ℕ) : O) • (a - b) = 0 := by
      simp only at hab
      rw [Nat.cast_smul_eq_nsmul, smul_sub, hab, sub_self]
    have h2 : a - b ∈ Submodule.torsion O M :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩, h1⟩
    rw [ht] at h2
    exact sub_eq_zero.1 h2
  exact Module.free_of_finite_type_torsion_free'

end DedekindLFunctions

theorem add_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone bar X → B' ∈ psdCone bar X → B + B' ∈ psdCone bar X := by
  intro O _ _ _ _ bar X _ _ _ B B' hB hB'
  obtain ⟨X₁, _, _, _, r₁, B₁, hr₁, hb₁, hd₁, he₁⟩ := hB
  obtain ⟨X₂, _, _, _, r₂, B₂, hr₂, hb₂, hd₂, he₂⟩ := hB'
  have : Module.Finite O X₁ := Module.Finite.of_surjective r₁ hr₁
  have : Module.Finite O X₂ := Module.Finite.of_surjective r₂ hr₂
  have ht₁ : Submodule.torsion O X₁ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have ht₂ : Submodule.torsion O X₂ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have : Module.Free ℤ X₁ := free_int_of_torsion_eq_bot O X₁ ht₁
  have : Module.Free ℤ X₂ := free_int_of_torsion_eq_bot O X₂ ht₂
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  have : Module.Finite ℤ X₂ := Module.Finite.trans O X₂
  have hdef := isPosDef_orthSum (Module.Free.chooseBasis ℤ X₁) (Module.Free.chooseBasis ℤ X₂) hd₁ hd₂
  let r : X →ₗ[O] X₁ × X₂ := r₁.prod r₂
  let P := LinearMap.range r
  have htP : Submodule.torsion O P = ⊥ := by
    have ht : Submodule.torsion O (X₁ × X₂) = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨a, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    have h1 : (u : X₁ × X₂) ∈ Submodule.torsion O (X₁ × X₂) :=
      (Submodule.mem_torsion_iff _).2 ⟨a, by simpa using congrArg Subtype.val hau⟩
    rw [ht] at h1
    exact Subtype.ext h1
  have : Module.Flat O P := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htP
  have : Module.FinitePresentation O P := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O P := Module.Flat.projective_of_finitePresentation
  let j : P →ₗ[ℤ] X₁ × X₂ := P.subtype.toAddMonoidHom.toIntLinearMap
  refine ⟨P, inferInstance, inferInstance, hproj, r.rangeRestrict, (orthSum B₁ B₂).compl₁₂ j j,
    r.surjective_rangeRestrict, ⟨fun y z => ?_, fun a y z => ?_⟩,
    isPosDef_compl_injective hdef j Subtype.val_injective, fun a b => ?_⟩
  · change B₁ _ _ + B₂ _ _ = B₁ _ _ + B₂ _ _
    rw [hb₁.1, hb₂.1]
  · change B₁ (a • _) _ + B₂ (a • _) _ = B₁ _ (bar a • _) + B₂ _ (bar a • _)
    rw [hb₁.2, hb₂.2]
    rfl
  · change B a b + B' a b = B₁ (r₁ a) (r₁ b) + B₂ (r₂ a) (r₂ b)
    rw [he₁, he₂]

end GlobalTheory.CompanionTheory.Ar.Fan
