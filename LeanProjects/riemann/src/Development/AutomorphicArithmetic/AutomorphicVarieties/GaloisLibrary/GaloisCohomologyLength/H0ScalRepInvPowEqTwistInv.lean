import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem units_zpow_neg_smul_eq_self_iff (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[l] A]
    (v : ℤ_[l]ˣ) (e : ℤ) (x : A) :
    ((v ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ e.natAbs) • x = x := by
  have key : ∀ n : ℕ, ((v ^ (-(n:ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ n) • x = x := by
    intro n
    rw [← Units.val_pow_eq_pow_val, ← Units.smul_def, ← Units.smul_def, zpow_neg, zpow_natCast]
    constructor
    · intro h
      conv_lhs => rw [← h]
      simp
    · intro h
      conv_lhs => rw [← h]
      simp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · simpa using key n
  · simp [← Units.val_pow_eq_pow_val]

theorem UpperTheory.V.LDataCardLeFinrank.H0_scalRep_inv_pow_eq_twistInv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (e : ℤ), H0 (scalRep (QZ l) (ψ ^ (-e))) = KStar.TotallyRealRoots.twistInv l (QZ l) ψ.range e.natAbs := by
  intro l _ Γ _ ψ e
  ext x
  rw [KStar.TotallyRealRoots.mem_twistInv]
  change (∀ g : Γ, (scalRep (QZ l) (ψ ^ (-e))) g x = x) ↔ _
  simp only [scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
    MonoidHom.zpow_apply]
  constructor
  · rintro h u ⟨g, rfl⟩
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mp (h g)
  · intro h g
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mpr (h _ ⟨g, rfl⟩)
