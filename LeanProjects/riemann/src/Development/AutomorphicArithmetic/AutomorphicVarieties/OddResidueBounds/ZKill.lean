import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ResKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.TotKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.NearLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ContinuousToTorsionBounded

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.zKill :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℕ) (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → 1 ≤ e → Procyc E Ω l → l ∣ N → ∀ (a : ℕ) (ha : a.Coprime N), Odd a → ∃ z : MonoidAlgebra ℤ_[l] (Gq ρ), IsInt l z (yEl (e + 1) a ha (piQ ρ)⁻¹) ∧ ∀ x ∈ Sha D (e : ℤ), (actRep D (e : ℤ) ρ).asAlgebraHom z (N.totient • x) = 0 := by
  intro E Ω _ _ _ _ _ l _ D e N _ ρ hcyc he hpro hlN a ha hodd
  obtain ⟨z, hz, hcong⟩ := Odd.congr l (Gq ρ) N (piQ ρ)⁻¹ e a ha hodd hlN
  refine ⟨z, hz, fun x hx => ?_⟩
  obtain ⟨r, hr⟩ := (Z1_H1_qz_twist_l_power_torsion E Ω l D (e : ℤ)).2 x
  obtain ⟨m₁, hm₁⟩ := hcong r
  have hal : a.Coprime (N * l) := Nat.Coprime.mul_right ha (Nat.Coprime.coprime_dvd_right hlN ha)
  obtain ⟨m₂, hm₂⟩ := resKill E Ω l D e N ρ hcyc a hodd hal x hx
  set m := max m₁ m₂
  haveI : NeZero (N * l ^ m) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hNM : N ∣ N * l ^ m := Dvd.intro _ rfl
  obtain ⟨w, hw⟩ := hm₁ m (le_max_left _ _) (N * l ^ m) hNM rfl
  have hres := hm₂ m (le_max_right _ _) (N * l ^ m) hNM rfl
  rw [hw] at hres
  have hzero : ((actRep D (e : ℤ) ρ).asAlgebraHom ((l : ℤ_[l]) ^ r • w)) x = 0 := by
    rw [map_smul, LinearMap.smul_apply, ← LinearMap.map_smul, hr, map_zero]
  have he0 : (e : ℤ) ≠ 0 := by omega
  have htot := totKill E Ω l D (e : ℤ) N he0 hpro (((actRep D (e : ℤ) ρ).asAlgebraHom z) x) (fun u hu => by
    have h1 := hres u hu
    rwa [map_add, LinearMap.add_apply, hzero, add_zero] at h1)
  rw [map_nsmul]
  exact htot
