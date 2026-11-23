import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.pairZero :
    UpperTheory.V.Af.Gk.PairZero := by
  intro F _ _ _ π
  have hs : ∀ g h : GlobalTheory.CuspRep.GA F 0, g = h := fun g h => Units.ext (Subsingleton.elim _ _)
  let e : π.V →ₗ[ℂ] ℂ := (LinearMap.proj 1) ∘ₗ (Sm F 0).subtype ∘ₗ π.V.subtype
  have he : ∀ φ, e φ = φ.1.1 1 := fun _ => rfl
  have hinj : ∀ φ, e φ = 0 → φ = 0 := fun φ h =>
    Subtype.ext <| Subtype.ext <| funext fun g => by rw [hs g 1]; exact h
  have hfin : ∀ k φ, e (π.op (.fin k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hcpt : ∀ k φ, e (π.op (.cpt k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hlie : ∀ X φ, e (π.op (.lie X) φ) = 0 := fun X φ => by
    rw [Subsingleton.elim X 0]
    exact map_zero (fderiv ℝ (chart φ.1.1 1) (oneL F 0))
  refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ e e, fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)),
    fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)), fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · change e _ * e _ = e φ * e ψ
    rw [hfin, hfin]
  · change e _ * e _ = e φ * e ψ
    rw [hcpt, hcpt]
  · change e _ * e _ + e _ * e _ = 0
    rw [hlie, hlie, zero_mul, mul_zero, add_zero]
