import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import ReciprocityTheory.Hypotheses.GalCoh

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

theorem cycMod_eq_one_of_mem_Ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cycMod F Ω l r σ = 1 := by
  apply Units.ext
  have e := cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) r
  simp only [Nat.cast_one, map_one] at e
  simpa [cycMod] using e

theorem tame_vanish : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  intro _ hTD hEC F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v rho hA hl hrho hex
  obtain ⟨γ, hγI, hγ⟩ := hex

  have h0 : H0 rho = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : rho γ m = m := (Representation.mem_invariants rho m).mp hm γ
    apply hγ.1
    show rho γ m - m = rho γ 0 - 0
    rw [h1, map_zero, sub_self, sub_self]

  set χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype with hχdef
  have hχ : χ γ = 1 := cycMod_eq_one_of_mem_Ine 1 hl hA hγI
  have hdual : Subsingleton (H0 ((twDual χ rho).comp (MonoidHom.id _))) := by
    have key : ∀ φ ∈ H0 ((twDual χ rho).comp (MonoidHom.id _)), φ = 0 := by
      intro φ hφ
      have h1 : twDual χ rho γ φ = φ := (Representation.mem_invariants _ φ).mp hφ γ
      ext x
      obtain ⟨m, rfl⟩ := hγ.2 x
      have h3 := congrArg (fun ψ : TDual (ZMod (l ^ 1)) M => ψ (rho γ m)) h1
      simp only [twDual_apply, hχ, Units.val_one, one_mul] at h3
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
      show φ (rho γ m - m) = 0
      exact (LinearMap.map_sub (φ : Module.Dual (ZMod (l ^ 1)) M) (rho γ m) m).trans (sub_eq_zero.mpr h3.symm)
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)

  have hTD' := hTD F Ω l 1 M A rho v Nat.one_pos hA hrho
  have hinj := hTD'.2.2.2.2.1
  have h2 : Subsingleton (H2 rho) := by
    refine ⟨fun x y => hinj ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]

  have hc0 : Nat.card (H0 rho) = 1 := by
    rw [h0]; exact Nat.card_unique
  have hc2 : Nat.card (H2 rho) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩
  have he := (hEC F Ω l 1 M A rho v Nat.one_pos hA hrho).2 hl
  have hc1 : Nat.card (H1 rho) = 1 := by rw [he, hc0, hc2]
  exact ⟨h0, (Nat.card_eq_one_iff_unique.mp hc1).1, h2⟩

end GlobalTheory.StringRepresentationDecomposition
