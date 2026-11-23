import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAll

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinSupport

theorem exists_generalizedInverse {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) : ∃ g : W →ₗ[ℂ] V, Φ ∘ₗ g ∘ₗ Φ = Φ := by
  obtain ⟨r, hr⟩ := Φ.rangeRestrict.exists_rightInverse_of_surjective Φ.range_rangeRestrict
  obtain ⟨π, hπ⟩ := (LinearMap.range Φ).subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
  refine ⟨r ∘ₗ π, ?_⟩
  ext x
  have h1 : π (Φ x) = Φ.rangeRestrict x := LinearMap.congr_fun hπ (Φ.rangeRestrict x)
  have h2 : Φ.rangeRestrict (r (Φ.rangeRestrict x)) = Φ.rangeRestrict x :=
    LinearMap.congr_fun hr (Φ.rangeRestrict x)
  have h3 := congrArg Subtype.val h2
  simp only [LinearMap.comp_apply, h1]
  exact h3

theorem exists_reverse_intertwiner {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (Φ : V →ₗ[ℂ] W) (hΦ : Φ ≠ 0) (h : ∀ p, Φ ∘ₗ ρ p = σ p ∘ₗ Φ) :
    ∃ ψ : W →ₗ[ℂ] V, ψ ≠ 0 ∧ ∀ p, ψ ∘ₗ σ p = ρ p ∘ₗ ψ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := exists_generalizedInverse Φ
  let ψ : W →ₗ[ℂ] V := ∑ p : G, ρ p ∘ₗ g ∘ₗ σ p⁻¹
  have hinv : ∀ (p : G) (x : V), Φ (ρ p x) = σ p (Φ x) := fun p x => LinearMap.congr_fun (h p) x
  have hσ : ∀ (p : G) (w : W), σ p (σ p⁻¹ w) = w := fun p w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hρ : ∀ (p : G) (v : V), ρ p⁻¹ (ρ p v) = v := fun p v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hgx : ∀ x, Φ (g (Φ x)) = Φ x := fun x => LinearMap.congr_fun hg x
  have hterm : ∀ (p : G) (x : V), Φ (ρ p (g (σ p⁻¹ (Φ x)))) = Φ x := by
    intro p x
    have e : σ p⁻¹ (Φ x) = Φ (ρ p⁻¹ x) := (hinv p⁻¹ x).symm
    rw [hinv, e, hgx, hinv, hσ]
  have hψ : ∀ x, Φ (ψ (Φ x)) = (Fintype.card G : ℂ) • Φ x := by
    intro x
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, hterm, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨ψ, ?_, ?_⟩
  · intro h0
    apply hΦ
    ext x
    have h1 := hψ x
    rw [h0] at h1
    simp only [LinearMap.zero_apply, map_zero] at h1
    have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simpa [hc] using h1.symm
  · intro q
    ext w
    simp only [ψ, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q⁻¹) _ _ fun p => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ q), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem supportExistsAll : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by
  intro K _ _ _ ι _ _ _ τ hτ
  obtain ⟨s, b, lam, Φ, hb, hlam, hΦ, heq⟩ := GlobalTheory.CompanionTheory.TyFinJacquet.jacquetAll K ι τ hτ
  obtain ⟨ψ, hψ, hψeq⟩ := exists_reverse_intertwiner (PI.SerBridgeGLW.inflRep K b lam)
    (τ.ρ.comp (parab K b).subtype) Φ hΦ heq
  exact ⟨s, b, lam, hb, hlam, (PI.SerBridgeGLW.isConstituent_hc_iff K b lam τ).mpr ⟨ψ, hψ, hψeq⟩⟩

end GlobalTheory.CompanionTheory.TyFinSupport
