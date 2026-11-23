import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteCharNontrivial

theorem trace_eq_tau (I : AutInst) (x : I.E) :
    Algebra.trace ℚ I.E x = Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  have h1 : Algebra.trace ℚ I.E (star x) = Algebra.trace ℚ I.E x :=
    Algebra.trace_eq_of_algEquiv ((starRingAut : I.E ≃+* I.E).equivRatAlgEquiv _ _) x
  have h2 : Algebra.trace ℚ I.E (algebraMap I.F I.E (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) =
      2 * Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    rw [← Algebra.trace_trace (S := I.F), Algebra.trace_algebraMap, I.cm.deg2, map_nsmul, nsmul_eq_mul]
    norm_num
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, h1] at h2
  linarith

theorem exists_away {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (hg : g ≠ 0)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ j : 𝓞 E, j ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), g ∈ Q'.asIdeal → Q' ≠ Q → j ∈ Q'.asIdeal := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {g}}.Finite :=
    Ideal.finite_factors (by simpa using hg)
  have hch : ∀ v : HeightOneSpectrum (𝓞 E), ∃ a : 𝓞 E, a ∉ Q.asIdeal ∧ (v ≠ Q → a ∈ v.asIdeal) := by
    intro v
    by_cases hv : v = Q
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, fun h => (h hv).elim⟩
    · have hn : ¬ v.asIdeal ≤ Q.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hn
      exact ⟨a, ha', fun _ => ha⟩
  choose a ha ha' using hch
  refine ⟨∏ v ∈ hfin.toFinset, a v, ?_, ?_⟩
  · have := Q.isPrime
    intro h
    obtain ⟨v, -, hv⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ha v hv
  · intro Q' hQ' hne
    have hm : Q' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hQ'
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hm) (ha' Q' hne)

theorem core (I : AutInst) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) (Q : HeightOneSpectrum (𝓞 I.E)) (hgQ : ((g : ℕ) : 𝓞 I.E) ∈ Q.asIdeal)
    (hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal) (j : 𝓞 I.E) (hj : j ∉ Q.asIdeal) :
    ∃ z : 𝓞 I.E, psiEf (divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (algebraMap (𝓞 I.E) I.E (j * z)))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hgE : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have htr : ∀ z : 𝓞 I.E, ∃ n : ℤ, Algebra.trace ℚ I.E
      ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) = n := by
    intro z
    have e : divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E (j * z))) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
          ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) := by
      have e1 : algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((g : I.F)⁻¹) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((g : I.E)⁻¹) := by
        rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
        rfl
      rw [divN, e1, ← RingHom.map_mul, RingHom.map_mul (algebraMap (𝓞 I.E) I.E), mul_assoc]
    have h1 := hcon z
    rw [e] at h1
    have h2 := hrat ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z)
    rw [h1, one_mul] at h2
    rw [trace_eq_tau]
    exact PsiCondAllPf.trace_of_psi I _ h2
  obtain ⟨d, hd, hdQ⟩ := PsiCondAllPf.exists_diff_not_mem Q hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int _ htr d hd
  have hcg : (g : 𝓞 I.E) * c = j * d := by
    apply RingOfIntegers.coe_injective
    rw [RingHom.map_mul, RingHom.map_mul, hc, map_natCast]
    field_simp
  have hm : j * d ∈ Q.asIdeal := hcg ▸ Ideal.mul_mem_right _ _ hgQ
  rcases Q.isPrime.mem_or_mem hm with h | h
  exacts [hj h, hdQ h]

theorem exists_psi_ne_one : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  intro D psiEf _ _ hrat Q hQ
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    have hQ' := hQ
    rw [Nat.cast_mul] at hQ'
    rcases Q.isPrime.mem_or_mem hQ' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) Q hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.E D.host.E (D.host.g_prime i) (D.nd.g_split i) Q hi).1
  obtain ⟨j, hj, hj'⟩ := exists_away ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.2 hg) Q
  obtain ⟨z, hz⟩ := core (instOf D) psiEf hrat _ hg Q hQ hun j hj
  let z' : 𝓞 D.host.E := z
  refine ⟨oToS D.host.F D.host.E (j * z'), fun Q' h1 h2 => ?_, hz⟩
  rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hj' Q' h1 h2)

end GlobalTheory.FiniteCharNontrivial
