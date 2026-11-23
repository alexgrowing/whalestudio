import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem func_eq_lam : ∀ (S : Set (ℕ → ℂ)) (B : ℕ) (φ : (ℕ → ℂ) → ℂ), 0 ∈ S → (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ φ (a + b) = φ a + φ b) → (∀ c : ℂ, ∀ a ∈ S, c • a ∈ S ∧ φ (c • a) = c * φ a) → (∀ a ∈ S, (∀ n < B, a n = 0) → a = 0) → ∃ c : ℕ → ℂ, ∀ a ∈ S, φ a = lam B c a := by
  intro S B φ h0 hadd hsmul hdet
  classical
  let W : Submodule ℂ (ℕ → ℂ) :=
    { carrier := S
      add_mem' := fun {a b} ha hb => (hadd a ha b hb).1
      zero_mem' := h0
      smul_mem' := fun c a ha => (hsmul c a ha).1 }
  let φW : W →ₗ[ℂ] ℂ :=
    { toFun := fun a => φ a
      map_add' := fun a b => (hadd a a.2 b b.2).2
      map_smul' := fun c a => (hsmul c a a.2).2 }
  let r : W →ₗ[ℂ] (Fin B → ℂ) :=
    { toFun := fun a i => (a : ℕ → ℂ) i
      map_add' := fun a b => by ext i; rfl
      map_smul' := fun c a => by ext i; rfl }
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    refine hdet a a.2 (fun n hn => ?_)
    have := congrFun ha ⟨n, hn⟩
    simpa [r] using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective r hr
  let ψ : (Fin B → ℂ) →ₗ[ℂ] ℂ := φW.comp g
  refine ⟨fun n => if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0, fun a ha => ?_⟩
  have h1 : φ a = ψ (r ⟨a, ha⟩) := by
    show φW ⟨a, ha⟩ = φW (g (r ⟨a, ha⟩))
    rw [← LinearMap.comp_apply g r, hg, LinearMap.id_apply]
  rw [h1, LinearMap.pi_apply_eq_sum_univ ψ (r ⟨a, ha⟩), EisM.lam,
    Finset.sum_range (fun n => (if h : n < B then ψ (Pi.single ⟨n, h⟩ 1) else 0) * a n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [i.2, dif_pos, Fin.eta, r, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  have hs : (fun j : Fin B => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs, mul_comm]

end GlobalTheory
