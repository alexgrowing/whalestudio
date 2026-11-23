import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceLeEigenspacePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem wtSpace_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) ∧ ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a
  refine ⟨fun k σ v hv => ?_, fun k v hv => ?_⟩
  · have hd : deg (σ * frob h * σ⁻¹) = deg (frob h) := by
      simp [map_mul, map_inv]
    have he : ∀ u, a.ρ σ (a.ρ (frob h) u) = a.ρ (σ * frob h * σ⁻¹) (a.ρ σ u) := by
      intro u
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_assoc,
        inv_mul_cancel, mul_one]
    have := map_absSpace_le (a.ρ σ) he _ ⟨v, hv, rfl⟩
    unfold wtSpace
    rwa [absSpace_eq_of_deg_eq E Ω A w h V a _ _ hd] at this
  · have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans (one_lt_normV w))
    have hr : ((normV w : ℕ) : ℝ) ^ (((k + 2 : ℤ) : ℝ) / 2) =
        ((normV w : ℕ) : ℝ) * ((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
      rw [show (((k + 2 : ℤ) : ℝ) / 2) = (k : ℝ) / 2 + 1 by push_cast; ring,
        Real.rpow_add hq, Real.rpow_one, mul_comm]
    unfold wtSpace at hv ⊢
    rw [hr]
    have key : absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2)) ≤
        (absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) * ((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2))).comap
          a.N := by
      refine iSup₂_le fun α hα u hu => ?_
      have hN := a.map_N_eigenspace deg_frob hu
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem (((normV w : ℕ) : ℂ) * α) (Submodule.mem_iSup_of_mem ?_ hN)
      rw [norm_mul, hα, Complex.norm_natCast]
    exact key hv
end GlobalTheory.WeilDeligne.PrimDecomp
