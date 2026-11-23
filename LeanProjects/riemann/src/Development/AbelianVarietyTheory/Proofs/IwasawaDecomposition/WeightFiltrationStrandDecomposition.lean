import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp.SubStab

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem rho_pow_N_apply (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) :
    a.ρ σ ((a.N ^ j) v) = (((normV w : ℕ) : ℂ) ^ deg σ) ^ j • (a.N ^ j) (a.ρ σ v) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, a.comm_apply, ih, map_smul, smul_smul,
      Module.End.mul_apply, pow_succ']

theorem rho_mem_ker_pow (a : WDRep h V) (σ : Weil h) (j : ℕ) (v : V) (hv : (a.N ^ j) v = 0) :
    (a.N ^ j) (a.ρ σ v) = 0 := by
  have h1 := rho_pow_N_apply a σ⁻¹ j (a.ρ σ v)
  have h2 : a.ρ σ⁻¹ (a.ρ σ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h2, hv, smul_zero] at h1
  have h3 : a.ρ σ (a.ρ σ⁻¹ ((a.N ^ j) (a.ρ σ v))) = (a.N ^ j) (a.ρ σ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← h3, h1, map_zero]

theorem pow_N_mem_wtSpace (a : WDRep h V)
    (hN : ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) (j : ℕ) (k : ℤ) (v : V)
    (hv : v ∈ wtSpace a k) : (a.N ^ j) v ∈ wtSpace a (k + 2 * (j : ℤ)) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    have e : k + 2 * ((j + 1 : ℕ) : ℤ) = (k + 2 * (j : ℤ)) + 2 := by push_cast; ring
    rw [e, pow_succ', Module.End.mul_apply]
    exact hN _ _ ih

theorem strand_and_lowPart_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) → (∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m) ∧ IsSubWD a (lowPart (wtSpace a) a.N m) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hρ hN htop
  refine ⟨⟨fun σ => ?_, ?_⟩, ⟨fun σ => ?_, ?_⟩⟩
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap (a.ρ σ)
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [rho_pow_N_apply]
    refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨a.ρ σ s, hρ _ σ s hs, rfl⟩)
  ·
    show strand a.N (wtSpace a (-(m : ℤ))) m ≤ (strand a.N (wtSpace a (-(m : ℤ))) m).comap a.N
    refine iSup_le fun j => ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [Submodule.mem_comap]
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hj : (j : ℕ) < m
    · exact Submodule.mem_iSup_of_mem (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 1)) ⟨s, hs, rfl⟩
    · have hjm : (j : ℕ) = m := by have := j.isLt; omega
      have hmem := pow_N_mem_wtSpace a hN ((j : ℕ) + 1) _ s hs
      rw [htop _ (by push_cast; omega), Submodule.mem_bot] at hmem
      rw [hmem]
      exact Submodule.zero_mem _
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap (a.ρ σ)
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    exact Submodule.mem_iSup_of_mem k ⟨hρ k σ v hv1, rho_mem_ker_pow a σ _ v hv2⟩
  ·
    show lowPart (wtSpace a) a.N m ≤ (lowPart (wtSpace a) a.N m).comap a.N
    refine iSup_le fun k => ?_
    rintro v ⟨hv1, hv2⟩
    refine Submodule.mem_iSup_of_mem (k + 2) ⟨hN k v hv1, ?_⟩
    show (a.N ^ (((m : ℤ) - (k + 2) + 1) / 2).toNat) (a.N v) = 0
    have hv2' : (a.N ^ (((m : ℤ) - k + 1) / 2).toNat) v = 0 := hv2
    have hle : (((m : ℤ) - k + 1) / 2).toNat ≤ (((m : ℤ) - (k + 2) + 1) / 2).toNat + 1 := by omega
    rw [← Module.End.mul_apply, ← pow_succ, ← Nat.sub_add_cancel hle, pow_add,
      Module.End.mul_apply, hv2', map_zero]

end GlobalTheory.WeilDeligne.PrimDecomp.SubStab
