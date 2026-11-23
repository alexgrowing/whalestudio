import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem iotaMulti_ne_zero_of_linearIndependent {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}
    {b : Fin r → V} (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem exists_unit_of_span_eq {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (R : Subring Ω) {c m : W}
    (hm : m ≠ 0) (h : Submodule.span R {c} = Submodule.span R {m}) :
    ∃ u : Ω, u ≠ 0 ∧ u ∈ R ∧ u⁻¹ ∈ R ∧ c = u • m := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self (R := R) c)
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h.symm ▸ Submodule.mem_span_singleton_self (R := R) m)
  have hu' : (u : Ω) • m = c := hu
  have hv' : (v : Ω) • c = m := hv
  have h1 : ((v : Ω) * u - 1) • m = 0 := by
    rw [sub_smul, mul_smul, hu', hv', one_smul, sub_self]
  have h2 : (v : Ω) * u = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hm)
  have h3 : (u : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine ⟨u, h3, u.2, ?_, hu'.symm⟩
  rw [inv_eq_of_mul_eq_one_left h2]
  exact v.2

theorem exists_coeff_regular_of_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  intro X Ω _ ξ V _ _ A B p q a b x b₁ b₂ hc f₁ f₂
  obtain ⟨α₀, β₀, hα, hβ, hA, hB, h1⟩ := hc
  rw [one_mul] at h1
  subst h1
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁] at hA
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂] at hB
  obtain ⟨u, -, hu, -, hau⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₁.1) hA.symm
  obtain ⟨t, ht0, -, hti, hbt⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₂.1) hB.symm
  refine ⟨u / α₀, t / α₀, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, mul_smul, ← hau, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · rw [div_eq_inv_mul, mul_smul, ← hbt, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · have : u / α₀ / (t / α₀) = u * t⁻¹ := by field_simp
    rw [this]
    exact mul_mem hu hti

end GlobalTheory.CompanionTheory.Ar.LocFn
