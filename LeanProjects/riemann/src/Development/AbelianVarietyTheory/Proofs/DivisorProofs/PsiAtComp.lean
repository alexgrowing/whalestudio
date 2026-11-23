import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TwAdmProof

theorem not_mem_sq_of_eWL {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : (p : 𝓞 E) ∈ w.asIdeal) (he : eWL E w = 1) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he' : P.ramificationIdx ℤ = 1 := he
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he'
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he'
  rw [hmap, Ideal.span_le]
  simpa using h2

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem not_mem_of_dvd (P : PlE D.host) (he : eWL D.host.E P = 1) {p : ℕ} (hp : p.Prime)
    (h : p ∣ D.host.QS * D.host.q * D.host.d) : (p : 𝓞 D.host.E) ∉ P.asIdeal := fun hv =>
  not_mem_sq_of_eWL hp P hv he (UpperTheory.Ram.mem_sq_of_dvd_condN D.host hp h _ P.isPrime hv)

theorem two_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he Nat.prime_two ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _)

theorem d_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.2.1 (dvd_mul_left _ _)

theorem q_not_mem (P : PlE D.host) (he : eWL D.host.E P = 1) : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal :=
  not_mem_of_dvd P he D.host.hyp.1 ((dvd_mul_left _ _).mul_right _)

end GlobalTheory.BigOn.Exp.TwAdmProof

namespace GlobalTheory.BigOn.Exp.TwAdmProof

variable {D : D7}

theorem exists_splitK_of (P : PlE D.host) (h1 : P.asIdeal.inertiaDeg ℤ = 1) (he : eWL D.host.E P = 1) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have hp := GlobalTheory.TwistDet.prime_normV h1
  have hmem : ((Formalism.ConjugateSelfDual.normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2 : Ideal.absNorm P.asIdeal = Formalism.ConjugateSelfDual.normV P := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact h2 ▸ Ideal.absNorm_mem P.asIdeal
  have hodd : Odd (Formalism.ConjugateSelfDual.normV P) := by
    refine hp.eq_two_or_odd'.resolve_left fun e => two_not_mem P he ?_
    rw [e] at hmem; exact hmem
  refine GlobalTheory.TwistDet.exists_splitK h1 he hodd (fun h => q_not_mem P he h) (fun h => d_not_mem P he h)

theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (ψ : Γ →* A) (f : Γ' →* Γ) :
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b ψ).comp f = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ.comp f) := by
  cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.inv_comp]

end GlobalTheory.BigOn.Exp.TwAdmProof

open GlobalTheory.BigOn.Exp.TwAdmProof in

theorem GlobalTheory.BigOn.Exp.twAdm : TwAdm := by
  unfold TwAdm AtTw AtPts
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    EvPt.of_forall fun x hx i p hR _ w hw _ => ?_⟩⟩
  have hmu := (p.tw_iff w).1 hw
  obtain ⟨-, N0, S, hG⟩ := hR.ties.twist
  obtain ⟨-, hall⟩ := hG w hmu
  have h1 := hall 1 (by simp)
  rw [zpow_one] at h1
  have hpsi := h1.1
  refine ⟨?_, ?_, GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ _ (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois w hmu⟩
  · have h2 := Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt ((Fm.ex x hx i).nch.sd w) (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hpsi)
    rw [psiAt_comp, Formalism.MainNotions.psiAt_psiAt] at h2
    exact h2
  · intro P hP
    obtain ⟨-, hin, he⟩ := hpsi.1 P hP
    exact exists_splitK_of P hin he
