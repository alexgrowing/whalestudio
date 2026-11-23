import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.Base GlobalTheory.Ord2

namespace UpperTheory.V.Z.Kato

theorem Used.adm {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {e N : ℕ} {θ ψ : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (u : Used l Ω K e N θ ψ W)
    {ι : Qbar l ≃+* ℂ} {f : Af.Newform (2 * e + 1)} (hf : f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) :
    dt W = θ ∧ GlobalTheory.Ord2.admitted ι e W := by
  have hdt : dt W = θ := MonoidHom.ext fun g => Units.ext (u.det g)
  refine ⟨hdt, u.level.cont, ?_, fun s hs => ?_, ?_, ⟨_, ?_, u.level.away⟩, ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩, ?_⟩
  · rw [hdt]
    exact MonoidHom.ext u.θ_sq
  · rw [hdt]
    obtain ⟨φ, hφ⟩ := hs
    have himag := u.imag
    have h3 : (θ s : Qbar l) * θ s = 1 := by rw [← sq, ← Units.val_pow_eq_pow_val, u.θ_sq s, Units.val_one]
    refine Units.ext ((mul_self_eq_one_iff.1 h3).resolve_left fun h => ?_)
    have h1 : s ∈ galOf ℚ K Ω := u.θ_ker ▸ (Units.ext h : θ s = 1)
    refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]
  · refine IrrTransfer.isIrr_of_range _ _ ?_ u.irr
    rintro ⟨τ, hτ⟩
    have hmem : galEmb ℚ K Ω τ ∈ H0g W := by
      refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hτ : _), ?_⟩
      rw [hdt, u.θ_ker]
      exact galEmb_mem ℚ K Ω τ
    exact ⟨⟨_, hmem⟩, rfl⟩
  · exact Nat.mul_pos u.N_pos (Int.natAbs_pos.2 (discr_ne_zero K))
  · rw [mul_one]
    exact hf
  · rw [hdt]
    exact u.flag

end UpperTheory.V.Z.Kato
