import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem fixed_mem_F (hcm : IsCMExt F E σ) (e : E) (he : σ e = e) : ∃ f : F, algebraMap F E f = e := by
  obtain ⟨-, hE, hdeg, hconj⟩ := hcm
  by_contra hne
  have hbot : e ∉ (⊥ : IntermediateField F E) := by
    intro hmem
    obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hmem
    exact hne ⟨f, hf⟩
  have hint : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  have htop : (IntermediateField.adjoin F {e}) = ⊤ := by
    have hd : Module.finrank F (IntermediateField.adjoin F {e}) ∣ 2 := by
      have := IntermediateField.finrank_dvd_of_le_right (K := F) (le_top : (IntermediateField.adjoin F {e}) ≤ ⊤)
      rwa [IntermediateField.finrank_top', hdeg] at this
    have h1 : Module.finrank F (IntermediateField.adjoin F {e}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff]
      exact hbot
    have h22 : Module.finrank F (IntermediateField.adjoin F {e}) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h h1
      · exact h
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [h22, IntermediateField.finrank_top', hdeg]
  have hfix : ∀ x : E, σ x = x := by
    intro x
    have hx : x ∈ Algebra.adjoin F ({e} : Set E) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
      trivial
    have hle : Algebra.adjoin F ({e} : Set E) ≤ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [Algebra.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact he
    exact hle hx
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hE.isComplex w)
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  have h := hconj w.embedding x
  rw [hfix] at h
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h]

theorem sc_eq (a : Fv F v) : sc (E := E) v a = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [sc, Algebra.TensorProduct.algebraMap_apply]

theorem add_sig_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : ∃ t : Fv F v, z + sigR (Fv F v) σ z = sc (E := E) v t := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [sc_eq]⟩
  | tmul r e =>
    obtain ⟨f, hf⟩ := fixed_mem_F σ hcm (e + σ e) (by rw [map_add, sigma_invol σ hcm, add_comm])
    refine ⟨f • r, ?_⟩
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    rw [hs, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨t1, h1⟩ := hx
    obtain ⟨t2, h2⟩ := hy
    refine ⟨t1 + t2, ?_⟩
    rw [map_add, sc_eq, map_add, ← sc_eq, ← sc_eq, ← h1, ← h2]
    abel

theorem two_ne_zero_v : (2 : Fv F v) ≠ 0 := by
  have h : (2 : F) ≠ 0 := two_ne_zero
  intro h2
  apply h
  apply (algebraMap F (Fv F v)).injective
  rw [map_ofNat, map_zero]
  exact h2

theorem fix_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) :
    ∃ a : Fv F v, z = sc (E := E) v a := by
  obtain ⟨t, ht⟩ := add_sig_sc σ v hcm z
  rw [hz] at ht
  refine ⟨t / 2, ?_⟩
  rw [div_eq_inv_mul, ← sc_mul, ← ht, ← smul_eq_sc, ← two_smul (Fv F v) z, smul_smul,
    inv_mul_cancel₀ (two_ne_zero_v v), one_smul]

theorem one_mem_oEv : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using gen_mem (E := E) v 1

theorem sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  simpa using sc_mul_mem_oEv (E := E) v hc (one_mem_oEv v)

def oAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (by exact one_mem_oEv v)
    (fun _ _ hx hy => by exact oEv_mul v hx hy)

theorem sc_mem_int {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hle : OEv (E := E) v ⊆ {z | IsIntegral (v.adicCompletionIntegers F) z} := by
    show (Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) : Set (Fv F v ⊗[F] E)) ⊆ _
    intro z hz
    have hsp : Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) ≤
        (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F)) (inclR (F := F) (Fv F v))
        (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
    exact hsp hz
  have hint : IsIntegral (v.adicCompletionIntegers F) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) := by
    rw [← sc_eq]
    exact hle ha
  have hint' : IsIntegral (v.adicCompletionIntegers F) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E))
      (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  rw [← hy]
  exact y.2

theorem fix_int (hcm : IsCMExt F E σ) {z : Fv F v ⊗[F] E} (hz0 : z ∈ OEv (E := E) v) (hz : sigR (Fv F v) σ z = z) :
    ∃ a ∈ v.adicCompletionIntegers F, z = sc (E := E) v a := by
  obtain ⟨a, ha⟩ := fix_sc σ v hcm z hz
  exact ⟨a, sc_mem_int v (ha ▸ hz0), ha⟩

theorem isU_sc {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F)
    (hu : IsUnit (⟨a, ha⟩ : v.adicCompletionIntegers F)) : IsU v (sc (E := E) v a) := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨sc v ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), sc_mem v (SetLike.coe_mem _), ?_⟩
  have h1 : a * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) = 1 := by
    have h2 := congrArg (fun r : v.adicCompletionIntegers F => (r : Fv F v)) u.mul_inv
    rw [hu'] at h2
    simpa using h2
  rw [sc_mul, h1, sc_one]

private theorem fixLoc_holds_lemma {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (h : IsU (E := E) v (sc v c)) : IsUnit (⟨c, hc⟩ : v.adicCompletionIntegers F) := by
  obtain ⟨w, hw, hcw⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [sc_eq, map_zero, zero_mul] at hcw
    exact zero_ne_one hcw
  have hweq : w = sc v c⁻¹ := by
    have h1 : sc (E := E) v c⁻¹ * (sc v c * w) = sc v c⁻¹ := by rw [hcw, mul_one]
    rw [← mul_assoc, sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at h1
    exact h1
  have hinv : c⁻¹ ∈ v.adicCompletionIntegers F := sc_mem_int v (hweq ▸ hw)
  have hprod : (⟨c, hc⟩ : v.adicCompletionIntegers F) * ⟨c⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    simp [mul_inv_cancel₀ hc0]
  exact IsUnit.of_mul_eq_one _ hprod

theorem fixLoc_holds : FixLoc σ v := by
  intro hcm x hx y hy hfx hfy hu
  obtain ⟨a, ha, rfl⟩ := fix_int σ v hcm hx hfx
  obtain ⟨b, hb, rfl⟩ := fix_int σ v hcm hy hfy
  have hab : a + b ∈ v.adicCompletionIntegers F := add_mem ha hb
  rw [sc_eq, sc_eq, ← map_add, ← sc_eq] at hu
  have hU : IsUnit ((⟨a, ha⟩ : v.adicCompletionIntegers F) + ⟨b, hb⟩) := fixLoc_holds_lemma v hab hu
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h | h
  · exact Or.inl (isU_sc v ha h)
  · exact Or.inr (isU_sc v hb h)

end PI.OmLocU.UnN
