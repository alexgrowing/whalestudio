import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trace_restrict_sup_disjoint {V : Type} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (S S' : Submodule ℂ V) (hF : FiniteDimensional ℂ S) (hF' : FiniteDimensional ℂ S')
    (hd : Disjoint S S') (hS : ∀ x ∈ S, f x ∈ S) (hS' : ∀ x ∈ S', f x ∈ S')
    (hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S') :
    LinearMap.trace ℂ ↥(S ⊔ S') (f.restrict hT) =
      LinearMap.trace ℂ S (f.restrict hS) + LinearMap.trace ℂ S' (f.restrict hS') := by
  let φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S') :=
    ((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by
      simpa using Submodule.add_mem_sup p.1.2 p.2.2))
  have hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have h0 : (a : V) + (b : V) = 0 := by simpa [hφ] using congrArg Subtype.val h
    have ha : (a : V) ∈ S' := by
      have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact S'.neg_mem b.2
    have ha0 : (a : V) = 0 := (Submodule.disjoint_def.1 hd) _ a.2 ha
    have hb0 : (b : V) = 0 := by simpa [ha0] using h0
    ext <;> simp [ha0, hb0]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩
  let e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S') := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := fun p => hφ p
  have hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS')) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨p, rfl⟩ := e.surjective x
    have hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) =
        e ((f.restrict hS).prodMap (f.restrict hS') p) := by
      simp [LinearEquiv.conj_apply]
    rw [hc]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, he, he, map_add]
    rfl
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem UpperTheory.RealTr.trAdd :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V),
      (∀ S S' : Submodule ℂ V, FiniteDimensional ℂ S → FiniteDimensional ℂ S' → Disjoint S S' → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S', f x ∈ S') →
        trOn (S ⊔ S') f = trOn S f + trOn S' f) ∧
      (∀ (S : Submodule ℂ V) (g : Module.End ℂ V) (c : ℂ), (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, g x ∈ S) →
        trOn S (f + g) = trOn S f + trOn S g ∧ trOn S (c • f) = c * trOn S f ∧ ((∀ x ∈ S, f x = g x) → trOn S f = trOn S g)) ∧
      (∀ (S S' : Submodule ℂ V) (g : Module.End ℂ V), FiniteDimensional ℂ S → FiniteDimensional ℂ S' → (∀ x ∈ S, f x ∈ S') → (∀ x ∈ S', g x ∈ S) →
        trOn S (g * f) = trOn S' (f * g)) ∧
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → trOn S (1 : Module.End ℂ V) = Module.finrank ℂ S := by
  intro V _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hF hF' hd hS hS'
    have hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S' := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hS a ha) (hS' b hb)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos hT, dif_pos hS, dif_pos hS']
    exact trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT
  · intro S g c hf hg
    have hfg : ∀ x ∈ S, (f + g) x ∈ S := fun x hx => S.add_mem (hf x hx) (hg x hx)
    have hcf : ∀ x ∈ S, (c • f) x ∈ S := fun x hx => S.smul_mem c (hf x hx)
    refine ⟨?_, ?_, ?_⟩
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hfg, dif_pos hf, dif_pos hg, ← map_add]
      congr 1
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hcf, dif_pos hf]
      have : (c • f).restrict hcf = c • f.restrict hf := by ext x; simp
      rw [this, map_smul, smul_eq_mul]
    · intro he
      unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hf, dif_pos hg]
      congr 1
      ext x
      simp [he x x.2]
  · intro S S' g hF hF' hf hg
    have h1 : ∀ x ∈ S, (g * f) x ∈ S := fun x hx => hg _ (hf x hx)
    have h2 : ∀ x ∈ S', (f * g) x ∈ S' := fun x hx => hf _ (hg x hx)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1, dif_pos h2]
    let a : S →ₗ[ℂ] S' := f.restrict hf
    let b : S' →ₗ[ℂ] S := g.restrict hg
    have e1 : (g * f).restrict h1 = b ∘ₗ a := by ext x; rfl
    have e2 : (f * g).restrict h2 = a ∘ₗ b := by ext x; rfl
    rw [e1, e2]
    exact LinearMap.trace_comp_comm' a b
  · intro S hF
    have h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S := fun x hx => hx
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1]
    have : (1 : Module.End ℂ V).restrict h1 = LinearMap.id := by ext x; rfl
    rw [this, LinearMap.trace_id]
