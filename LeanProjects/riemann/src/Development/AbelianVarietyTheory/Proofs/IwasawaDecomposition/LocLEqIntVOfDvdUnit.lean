import Mathlib
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalRingCardinality.DataLevel
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_inv_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    ((T : v.adicCompletion F) ≠ 0) ∧ (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (((T : 𝓞 F) : F) : v.adicCompletion F) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).2 hT
  have h2 : (((T : 𝓞 F) : F) : v.adicCompletion F) = (T : v.adicCompletion F) := by
    have : ((T : 𝓞 F) : F) = (T : F) := by push_cast; rfl
    rw [this]
    exact map_natCast (algebraMap F (v.adicCompletion F)) T
  rw [h2] at h1
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨hne, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem locL_eq_intV_of_dvd_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop)
    (π c : 𝓞 E) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (hπc : π * c = (T : 𝓞 E))
    (hΛ : ∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  classical
  have hleft : ∀ r : 𝓞 E, ((r : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Formalism.BasicNotions.intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)
  have hright : ∀ t ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] t) ∈ Formalism.BasicNotions.intV E v := fun t ht =>
    Subring.subset_closure (Or.inr ⟨⟨t, ht⟩, rfl⟩)
  constructor
  · intro hy
    let M : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
      { carrier := {y | ∀ a, y a ∈ Formalism.BasicNotions.intV E v}
        add_mem' := fun ha hb a => (Formalism.BasicNotions.intV E v).add_mem (ha a) (hb a)
        zero_mem' := fun _ => (Formalism.BasicNotions.intV E v).zero_mem
        smul_mem' := fun s _ hy a => (Formalism.BasicNotions.intV E v).mul_mem s.2 (hy a) }
    have hle : Formalism.L2.Herm.locL v Λ ≤ M := by
      unfold Formalism.L2.Herm.locL Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ a
      obtain ⟨r, hr, -⟩ := (hΛ x).1 hx a
      show Formalism.UG.inclE _ (x a) ∈ Formalism.BasicNotions.intV E v
      rw [hr]; exact hleft r
    exact hle hy
  · intro hy
    obtain ⟨_, hinv⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
    have he : ∀ a, (Pi.single a (1 : E ⊗[F] v.adicCompletion F)) ∈ Formalism.L2.Herm.locL v Λ := by
      intro a
      have hx : (Pi.single a ((π : 𝓞 E) : E) : Fin n → E) ∈ Λ := by
        rw [hΛ]
        intro b
        refine ⟨(Pi.single a π : Fin n → 𝓞 E) b, ?_, fun _ => ?_⟩
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
      have hg : (Pi.single a (((π : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) : Fin n → _) ∈
          Formalism.L2.Herm.locL v Λ := by
        unfold Formalism.L2.Herm.locL Formalism.UG.latS
        apply Submodule.subset_span
        refine ⟨_, hx, ?_⟩
        funext b
        by_cases h : b = a
        · subst h; simp [Formalism.UG.inclE]
        · simp [h, Formalism.UG.inclE]
      let s : Formalism.BasicNotions.intV E v :=
        ⟨((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹),
          (Formalism.BasicNotions.intV E v).mul_mem (hleft c) (hright _ hinv)⟩
      have hs : (s : E ⊗[F] v.adicCompletion F) * ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1 := by
        obtain ⟨hne, -⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
        show ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) *
          ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hcπ : (c : E) * (π : E) = (T : E) := by
          rw [mul_comm]; exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hπc
        rw [hcπ]
        have hT1 : (T : E) ⊗ₜ[F] (1 : v.adicCompletion F) = (1 : E) ⊗ₜ[F] (T : v.adicCompletion F) := by
          have e1 := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
            (B := v.adicCompletion F)) T
          have e2 := map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E)
            (B := v.adicCompletion F)) T
          rw [Algebra.TensorProduct.includeLeftRingHom_apply] at e1
          rw [Algebra.TensorProduct.includeRight_apply] at e2
          rw [e1, e2]
        calc (T : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹
            = ((T : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = 1 := by
              rw [hT1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
              rfl
      have := (Formalism.L2.Herm.locL v Λ).smul_mem s hg
      convert this using 1
      funext b
      by_cases h : b = a
      · subst h
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, Pi.single_eq_same, hs]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
    have hsum : y = ∑ a, (⟨y a, hy a⟩ : Formalism.BasicNotions.intV E v) • Pi.single a (1 : E ⊗[F] v.adicCompletion F) := by
      funext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one]
      · intro a _ hab
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hab), mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (he a)

end GlobalTheory
