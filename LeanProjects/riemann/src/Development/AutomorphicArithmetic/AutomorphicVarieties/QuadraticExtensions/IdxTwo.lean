import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.InvTwo

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem idxTwo_conj {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U : Subgroup Γ) (S : Set Γ)
    (σ : Γ) (n : ℕ) (hc : ∀ u ∈ U, σ⁻¹ * u * σ ∈ U) (h2 : σ * σ ∈ U) (hS : ∀ s ∈ S, σ⁻¹ * s * σ ∈ S)
    (h : CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n) :
    CardLe (CharOff U S 2) (n ^ 2) := by
  let c : U → U := fun u => ⟨σ⁻¹ * u.1 * σ, hc u.1 u.2⟩
  have hcc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hcm : ∀ a b : U, c (a * b) = c a * c b := by
    intro a b
    apply Subtype.ext
    show σ⁻¹ * (a.1 * b.1) * σ = σ⁻¹ * a.1 * σ * (σ⁻¹ * b.1 * σ)
    group
  have hmem : ∀ φ : CharOff U S 2, (fun u => φ.1 u + φ.1 (c u)) ∈ CharOff U S 2 := by
    intro φ
    obtain ⟨hl, hadd, hz⟩ := φ.2
    refine ⟨hl.add (hl.comp_continuous hcc), fun a b => ?_, fun u hu => ?_⟩
    · simp only [hcm, hadd]
      ring
    · simp only [hz u hu, hz (c u) (hS _ hu), add_zero]
  let f : CharOff U S 2 →+ CharOff U S 2 :=
    { toFun := fun φ => ⟨_, hmem φ⟩
      map_zero' := by
        apply Subtype.ext
        funext u
        simp
      map_add' := by
        intro a b
        apply Subtype.ext
        funext u
        simp only [Submodule.coe_add, Pi.add_apply]
        ring }
  have hff : ∀ x, f (f x) = 0 := by
    intro φ
    obtain ⟨-, hadd, -⟩ := φ.2
    have h1 : φ.1 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      linear_combination -this
    have hcc' : ∀ u, φ.1 (c (c u)) = φ.1 u := by
      intro u
      have : c (c u) = (⟨σ * σ, h2⟩ : U)⁻¹ * u * ⟨σ * σ, h2⟩ := by
        apply Subtype.ext
        show σ⁻¹ * (σ⁻¹ * u.1 * σ) * σ = (σ * σ)⁻¹ * u.1 * (σ * σ)
        group
      have hinv : φ.1 (⟨σ * σ, h2⟩ : U)⁻¹ + φ.1 ⟨σ * σ, h2⟩ = 0 := by
        rw [← hadd, inv_mul_cancel, h1]
      rw [this, hadd, hadd]
      linear_combination hinv
    apply Subtype.ext
    funext u
    show φ.1 u + φ.1 (c u) + (φ.1 (c u) + φ.1 (c (c u))) = 0
    rw [hcc']
    generalize φ.1 u = a
    generalize φ.1 (c u) = b
    revert a b
    decide
  have hker : CardLe f.ker n := by
    refine CardLe.of_injective h (fun φ => ⟨φ.1, fun u u' hu => ?_⟩) ?_
    · have h0 : f φ.1 = 0 := φ.2
      have h3 : φ.1.1 u + φ.1.1 (c u) = 0 := congrArg (fun ψ : CharOff U S 2 => ψ.1 u) h0
      have hu' : u' = c u := Subtype.ext hu
      rw [hu']
      revert h3
      generalize φ.1.1 u = a
      generalize φ.1.1 (c u) = b
      revert a b
      decide
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext hab'
  exact sqZero _ f n hff hker

theorem UpperTheory.V.Two.idxTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (n : ℕ), U ≤ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V ∣ 2 → (∀ v ∈ V, ∀ s ∈ S, v⁻¹ * s * v ∈ S) → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe (CharOff U S 2) (n ^ 2) := by
  intro Γ _ _ _ U V S n hUV hopen hdvd hSV hSU hV
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · have hVU : V ≤ U := Subgroup.relIndex_eq_one.1 h1
    have : U = V := le_antisymm hUV hVU
    subst this
    exact hV.mono (Nat.le_self_pow two_ne_zero n)
  · have hnot : ¬ V ≤ U := fun hle => by
      rw [Subgroup.relIndex_eq_one.2 hle] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨σ, hσV, hσU⟩ := SetLike.not_le_iff_exists.1 hnot
    have hidx : (U.subgroupOf V).index = 2 := h2
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    refine idxTwo_conj U S σ n ?_ ?_ (fun s hs => hSV σ hσV s hs)
      (invTwo Γ U V S σ n hUV hσV hopen h2 hσU hSU hV)
    · intro u hu
      have := hnorm.conj_mem ⟨u, hUV hu⟩ (Subgroup.mem_subgroupOf.2 hu) (⟨σ, hσV⟩⁻¹)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · have := Subgroup.mul_self_mem_of_index_two hidx ⟨σ, hσV⟩
      rwa [Subgroup.mem_subgroupOf] at this
