import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSum
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem ind_mem_SB (U : Subgroup G) (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) :
    ind U ∈ SB G := by
  have hcl : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen ho, ho⟩
  refine GroundTheory.LocalField.mem_schwartzBruhat.mpr ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ U
    · refine ⟨U, ho, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∈ U from hy]
    · refine ⟨(U : Set G)ᶜ, hcl.compl.isOpen, hx, fun y hy => ?_⟩
      simp [ind, Set.indicator, hx, show y ∉ U from hy]
  · refine HasCompactSupport.intro hc fun x hx => ?_
    simp [ind, Set.indicator, show x ∉ U from hx]

private theorem translate_mem_SB (a : SB G) (g : G) : (fun m => a.1 (m * g)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
  exact GroundTheory.LocalField.mem_schwartzBruhat.mpr
    ⟨h1.comp_continuous (continuous_mul_right g), h2.comp_homeomorph (Homeomorph.mulRight g)⟩

private theorem scale (B : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (s : Finset G) (hs : ∀ g ∈ s, g ∈ U)
    (hsum : ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b) :
    B a = (s.card : ℂ) * B a' := by
  let t : G → SB G := fun g => ⟨fun m => a'.1 (m * g⁻¹), translate_mem_SB a' g⁻¹⟩
  have hat : a = ∑ g ∈ s, t g := by
    apply Subtype.ext
    funext x
    rw [ha, hsum x, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    change ind U' (x * g⁻¹) = a'.1 (x * g⁻¹)
    rw [ha']
  have ht : ∀ g ∈ s, B (t g) = B a' := fun g hg =>
    hB g⁻¹ (U.inv_mem (hs g hg)) a' (t g) fun _ => rfl
  rw [hat, map_sum, Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]

variable [T2Space G]

private theorem cross_le (B C : SB G →ₗ[ℂ] ℂ) (U U' : Subgroup G) (hle : U' ≤ U)
    (hc : IsCompact (U : Set G)) (ho : IsOpen (U' : Set G)) (a a' : SB G) (ha : a.1 = ind U)
    (ha' : a'.1 = ind U')
    (hB : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → B b' = B b)
    (hC : ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → C b' = C b) :
    B a * C a' = B a' * C a := by
  obtain ⟨s, -, hs, hsum⟩ := cosetSum G U U' hle hc ho
  rw [scale B U U' s hs hsum a a' ha ha' hB, scale C U U' s hs hsum a a' ha ha' hC]
  ring

private theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (hL : Lgrp G) (act : G → V →ₗ[ℂ] V)
    (hact : ∀ f, {g | act g f = f} ∈ 𝓝 (1 : G)) (I : SB G →ₗ[ℂ] ℂ)
    (hI : ∀ (g : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U → I a ≠ 0)
    (β : V →ₗ[ℂ] SB G →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : G) f (a a' : SB G), (∀ m, a'.1 m = a.1 (m * g)) → β (act g f) a' = β f a) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ f := by

  have hinv : ∀ (f : V) (U : Subgroup G), (∀ g ∈ U, act g f = f) →
      ∀ g ∈ U, ∀ b b' : SB G, (∀ m, b'.1 m = b.1 (m * g)) → β f b' = β f b := by
    intro f U hf g hg b b' hb
    have := hβ g f b b' hb
    rwa [hf g hg] at this

  have hex : ∀ f f' : V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧
      (∀ g ∈ U, act g f = f) ∧ (∀ g ∈ U, act g f' = f') := by
    intro f f'
    obtain ⟨U, ho, hc, hsub⟩ := hL _ (Filter.inter_mem (hact f) (hact f'))
    exact ⟨U, ho, hc, fun g hg => (hsub hg).1, fun g hg => (hsub hg).2⟩

  have hcpt : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      IsCompact (U : Set G) := by
    intro U a ho ha
    obtain ⟨-, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.mp a.2
    refine IsCompact.of_isClosed_subset h2 (U.isClosed_of_isOpen ho) fun x hx => ?_
    refine subset_tsupport _ ?_
    rw [Function.mem_support, ha]
    simp [ind, Set.indicator, show x ∈ U from hx]

  have hcross : ∀ (f : V) (U₁ U₂ : Subgroup G) (a₁ a₂ : SB G), IsOpen (U₁ : Set G) →
      IsOpen (U₂ : Set G) → a₁.1 = ind U₁ → a₂.1 = ind U₂ → (∀ g ∈ U₁, act g f = f) →
      (∀ g ∈ U₂, act g f = f) → β f a₁ * I a₂ = β f a₂ * I a₁ := by
    intro f U₁ U₂ a₁ a₂ ho₁ ho₂ h₁ h₂ hf₁ hf₂
    have hc₁ := hcpt U₁ a₁ ho₁ h₁
    have hc₂ := hcpt U₂ a₂ ho₂ h₂
    have ho₃ : IsOpen ((U₁ ⊓ U₂ : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]
      exact ho₁.inter ho₂
    have hc₃ : IsCompact ((U₁ ⊓ U₂ : Subgroup G) : Set G) :=
      IsCompact.of_isClosed_subset hc₁ ((U₁ ⊓ U₂).isClosed_of_isOpen ho₃) fun x hx => hx.1
    let a₃ : SB G := ⟨ind (U₁ ⊓ U₂), ind_mem_SB _ ho₃ hc₃⟩
    have e₁ := cross_le (β f) I U₁ (U₁ ⊓ U₂) inf_le_left hc₁ ho₃ a₁ a₃ h₁ rfl
      (hinv f U₁ hf₁) fun g _ => hI g
    have e₂ := cross_le (β f) I U₂ (U₁ ⊓ U₂) inf_le_right hc₂ ho₃ a₂ a₃ h₂ rfl
      (hinv f U₂ hf₂) fun g _ => hI g
    have h₃ : I a₃ ≠ 0 := hne _ a₃ ho₃ rfl
    apply mul_right_cancel₀ h₃
    linear_combination I a₂ * e₁ - I a₁ * e₂
  choose W hWo hWc hWf _ using fun f : V => hex f f
  let A : V → SB G := fun f => ⟨ind (W f), ind_mem_SB _ (hWo f) (hWc f)⟩
  let Λ₀ : V → ℂ := fun f => β f (A f) / I (A f)
  have key : ∀ f (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → a.1 = ind U →
      (∀ g ∈ U, act g f = f) → β f a = I a * Λ₀ f := by
    intro f U a ho ha hf
    have h := hcross f U (W f) a (A f) ho (hWo f) ha rfl hf (hWf f)
    have hA : I (A f) ≠ 0 := hne _ (A f) (hWo f) rfl
    change β f a = I a * (β f (A f) / I (A f))
    field_simp
    linear_combination h
  have hadd : ∀ f f', Λ₀ (f + f') = Λ₀ f + Λ₀ f' := by
    intro f f'
    obtain ⟨U, ho, hc, h₁, h₂⟩ := hex f f'
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (f + f') = f + f' := fun g hg => by
      rw [map_add, h₁ g hg, h₂ g hg]
    rw [mul_add, ← key f U a ho rfl h₁, ← key f' U a ho rfl h₂, ← key (f + f') U a ho rfl hf,
      map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) f, Λ₀ (c • f) = c * Λ₀ f := by
    intro c f
    obtain ⟨U, ho, hc, h₁, -⟩ := hex f f
    let a : SB G := ⟨ind U, ind_mem_SB _ ho hc⟩
    have hIa : I a ≠ 0 := hne U a ho rfl
    apply mul_left_cancel₀ hIa
    have hf : ∀ g ∈ U, act g (c • f) = c • f := fun g hg => by
      rw [map_smul, h₁ g hg]
    rw [mul_left_comm, ← key f U a ho rfl h₁, ← key (c • f) U a ho rfl hf, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
  exact ⟨⟨⟨Λ₀, hadd⟩, fun c f => by simpa using hsmul c f⟩, key⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lamEx :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ (I : SB (SL v) →ₗ[ℂ] ℂ), InvI I → ∀ β : V →ₗ[ℂ] SB (SL v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (SL v)), (∀ m, a'.1 m = a.1 (m * g)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      ∃ Λ : V →ₗ[ℂ] ℂ, ∀ f (U : Subgroup (SL v)) (a : SB (SL v)), IsOpen (U : Set (SL v)) → a.1 = ind U →
        (∀ g ∈ U, ρ (Matrix.SpecialLinearGroup.toGL g) f = f) → β f a = I a * Λ f := by
  intro F _ _ v V _ _ ρ hρ I hI β hβ
  refine core (lgrp F v).1 (fun g => ρ (Matrix.SpecialLinearGroup.toGL g)) (fun f => ?_) I
    hI.right hI.ne β hβ
  have ho : IsOpen {g : SL v | ρ (Matrix.SpecialLinearGroup.toGL g) f = f} :=
    (hρ f).preimage Matrix.SpecialLinearGroup.continuous_toGL
  exact ho.mem_nhds (by simp)
