import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MultIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem mem_AFall_iff {ρ : Representation ℂ (GQ L n) W} {f : GAf L n → W} :
    f ∈ NG.AFall L n ρ ↔ (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g := Iff.rfl

theorem mem_HomG_iff {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    {Φ : S →ₗ[ℂ] (GAf L n → W)} :
    Φ ∈ NG.HomG ρ S ↔ (∀ f, Φ f ∈ NG.AFall L n ρ) ∧ ∀ (h : GAf L n) (f f' : S),
      (f' : GAf L n → W) = NG.rt L n h (f : GAf L n → W) → Φ f' = NG.rt L n h (Φ f) := Iff.rfl

theorem comp_mem_AFall {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x)) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) :
    (fun g => A (f g)) ∈ NG.AFall L n ρ' := by
  obtain ⟨h1, N, hN, h2⟩ := mem_AFall_iff.1 hf
  exact mem_AFall_iff.2 ⟨fun γ g => by simp only [h1 γ g, hA], N, hN, fun κ hκ g => by simp only [h2 κ hκ g]⟩

def transport {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) :
    NG.HomG ρ S →ₗ[ℂ] NG.HomG ρ' S' where
  toFun Φ := ⟨(LinearMap.compLeft A (GAf L n)).comp ((Φ : S →ₗ[ℂ] (GAf L n → W)).comp T), mem_HomG_iff.2
     ⟨fun f => comp_mem_AFall A hA ((mem_HomG_iff.1 Φ.2).1 (T f)),
      fun h f f' e => by
        have := (mem_HomG_iff.1 Φ.2).2 h (T f) (T f') (hT h f f' e)
        simp only [LinearMap.comp_apply]
        rw [this]
        rfl⟩⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp
  map_smul' c Φ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp

theorem transport_apply {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) (Φ : NG.HomG ρ S) (x : S') (g : GAf L n) :
    ((transport A hA T hT Φ : S' →ₗ[ℂ] (GAf L n → W')) x) g = A ((Φ : S →ₗ[ℂ] (GAf L n → W)) (T x) g) := rfl

theorem mult_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  rintro L _ _ _ n π π' ⟨⟨A, hA⟩, ⟨T, hT⟩⟩
  have hTs : ∀ (h : GAf L n) (g g' : π'.S), (g' : GAf L n → π'.W) = NG.rt L n h (g : GAf L n → π'.W) →
      ((T.symm g' : π.S) : GAf L n → π.W) = NG.rt L n h ((T.symm g : π.S) : GAf L n → π.W) := by
    intro h g g' hg
    have key := hT h (T.symm g) ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ rfl
    rw [LinearEquiv.apply_symm_apply, ← hg] at key
    have e2 : T ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ = g' := Subtype.ext key
    rw [← e2, LinearEquiv.symm_apply_apply]
  have hAs : ∀ γ x, A.symm (π'.ρ γ x) = π.ρ γ (A.symm x) := by
    intro γ x
    apply A.injective
    rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
  let F := transport (ρ := π.ρ) (ρ' := π'.ρ) A.toLinearMap hA T.symm.toLinearMap hTs
  let G := transport (ρ := π'.ρ) (ρ' := π.ρ) A.symm.toLinearMap hAs T.toLinearMap hT
  let e : NG.HomG π.ρ π.S ≃ₗ[ℂ] NG.HomG π'.ρ π'.S := LinearEquiv.ofLinear F G
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
  exact e.finrank_eq

end GlobalTheory.MultIso

end
