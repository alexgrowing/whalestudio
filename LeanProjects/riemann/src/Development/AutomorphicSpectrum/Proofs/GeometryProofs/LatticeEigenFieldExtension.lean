import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigLat

theorem mem_eigSp_iff' {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {x : W} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem sum_smul_of_eig {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {n : ℕ} (a c : Fin n → O) {x : W}
    (hx : ∀ b, ρ b x = τ b • x) :
    ∑ m, τ (c m) • ρ (a m) x = τ (∑ m, c m * a m) • x := by
  simp only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]

theorem span_inf_eigSp : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd
  obtain ⟨n, a, c, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir F
  have hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)
  have hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω) := by rw [hsum, map_intCast]
  have hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω) := by
    rw [RingHom.comp_apply, hσd]
  have hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0 := (map_ne_zero i).2 hd0

  let P : V → V := fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v

  let P' : Module.End Ω' V' := (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)
  have hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x := by
    intro x
    simp [P', LinearMap.sum_apply]
  have hPeig : ∀ v, P v ∈ eigSp ρ σ := by
    intro v
    refine mem_eigSp_iff'.2 fun b => ?_
    simp only [P]
    rw [map_smul, heq Ω V ρ σ b v, smul_comm]
  have hPL : ∀ v ∈ L, P v ∈ L := by
    intro v hv
    have h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L := by
      refine Submodule.sum_mem _ fun m _ => ?_
      exact L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)
    exact L.smul_mem ⟨_, hd⟩ h1
  have hjP : ∀ v, P' (j v) = j (P v) := by
    intro v
    rw [hP'apply]
    simp only [P]
    rw [hj.1, map_inv₀, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hj.1, hρ, RingHom.comp_apply]
  have hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x := by
    intro x hx
    rw [hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul,
      inv_mul_cancel₀ hid0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx2' : x ∈ eigSp ρ' (i.comp σ) := hx2
    have key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R'
        (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        rw [hjP]
        exact Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        have h1 : P' (r • y) = r • P' y := by
          rw [Subring.smul_def, Subring.smul_def, map_smul]
        rw [h1]
        exact Submodule.smul_mem _ r hy
    have h2 := key x hx1
    rwa [hP'id x hx2'] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := Submodule.mem_inf.1 he
    have he2' : e ∈ eigSp ρ σ := he2
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ eigSp ρ' (i.comp σ)
    refine mem_eigSp_iff'.2 fun b => ?_
    rw [hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigLat
