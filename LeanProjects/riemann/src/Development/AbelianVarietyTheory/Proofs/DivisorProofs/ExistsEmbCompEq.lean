import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.UnramEmb

theorem nonempty_emb (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ discr E) : Nonempty (E →+* KW p) := by
  have := span_prime_isMaximal p hp.out
  obtain ⟨P, hP, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hpP : (p : 𝓞 E) ∈ P := mem_of_liesOver p P
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  let Q : HeightOneSpectrum (𝓞 E) := ⟨P, hP.isPrime, fun e => hp0 (by rwa [e, Ideal.mem_bot] at hpP)⟩
  have : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    (not_dvd_discr_iff_forall_liesOver E (𝓞 E) (Nat.prime_iff_prime_int.1 hp.out)).1 h P hP hPo
  obtain ⟨n, i, -, -⟩ := GlobalTheory.GO.PlWitt.exists_good (p := p) Q hpP
  let a : GaloisField p n →ₐ[ZMod p] AlgebraicClosure (ZMod p) := IsAlgClosed.lift
  have hj : Function.Injective ((algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (KW p)).comp
      (WittVector.map a.toRingHom)) :=
    (IsFractionRing.injective _ _).comp (WittVector.map_injective _ a.toRingHom.injective)
  exact ⟨(IsFractionRing.lift (K := GlobalTheory.GO.PlWitt.Qn p n) hj).comp i⟩

theorem exists_emb_comp_eq (D : D7) (p : ℕ) [Fact p.Prime] (h : UnramE D p) (jc : KW p →+* ℂ)
    (g : D.R.GG) : ∃ τ : Emb D p, jc.comp τ = D.host.emb g := by
  obtain ⟨τ₀⟩ := nonempty_emb D.host.E p (fun hd => h (Int.natCast_dvd.1 hd))
  obtain ⟨g₀, hg₀⟩ := (factEmb D.R D.host).1.2 (jc.comp τ₀)
  refine ⟨τ₀.comp (D.host.sigmaOf (g₀⁻¹ * g) : D.host.E →+* D.host.E), ?_⟩
  rw [← RingHom.comp_assoc, ← hg₀]
  refine RingHom.ext fun x => ?_
  show D.host.φ₀ (D.host.sigmaOf g₀ (D.host.sigmaOf (g₀⁻¹ * g) x)) = D.host.φ₀ (D.host.sigmaOf g x)
  have : D.host.sigmaOf (g₀ * (g₀⁻¹ * g)) = D.host.sigmaOf g₀ * D.host.sigmaOf (g₀⁻¹ * g) :=
    map_mul (D.host.gal).symm _ _
  rw [mul_inv_cancel_left] at this
  rw [this]; rfl

end GlobalTheory.UnramEmb
