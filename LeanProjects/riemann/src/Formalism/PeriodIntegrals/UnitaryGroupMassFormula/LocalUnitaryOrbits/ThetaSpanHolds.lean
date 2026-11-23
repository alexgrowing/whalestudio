import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfSpan

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem ov_smul (a : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    a • y = sc (E := E) v (a : Fv F v) * y := by
  rw [← smul_eq_sc]; rfl

theorem iO_max (p : 𝓞 F) (hp : p ∈ v.asIdeal) :
    (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v p).mpr hp
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at h1
  exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).mpr h1

theorem thetaSpan_holds : ThetaSpan σ J ψ v := by
  intro _ _ θ hsp x hx
  classical
  let ι : 𝓞 E →+* Fv F v ⊗[F] E := (inclR (F := F) (Fv F v)).comp (algebraMap (𝓞 E) E)
  let Nt : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ (ι '' Set.range (RingOfIntegers.basis E))
  let M : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ {(1 : Fv F v ⊗[F] E), inclR (F := F) (Fv F v) (θ : E)}
  have halg : ∀ b : 𝓞 F, ι (algebraMap (𝓞 F) (𝓞 E) b) = sc (E := E) v (iO v b) := by
    intro b
    show inclR (F := F) (Fv F v) (algebraMap F E (b : F)) = _
    rw [inclR_alg']
  have hN : ∀ y : 𝓞 E, ι y ∈ Nt := by
    intro y
    have hy : y ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by
      rw [(RingOfIntegers.basis E).span_eq]
      trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact Nt.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact Nt.add_mem ha hb
    | smul n a _ ha => rw [map_zsmul]; exact zsmul_mem ha n
  have hI : ∀ w ∈ IE (E := E) v, ∀ c : 𝓞 E,
      ι (c * w) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, rfl⟩ := hz
      intro c
      have hs := (ov_smul (E := E) v (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) (ι c)).symm
      rw [map_mul, halg, mul_comm]
      rw [hs]
      exact Submodule.smul_mem_smul (iO_max v p hp) (hN c)
    | zero => intro c; rw [mul_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => intro c; rw [mul_add, map_add]; exact Submodule.add_mem _ (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact ha (c * d)
  have hNM : Nt ≤ M ⊔ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    rw [Submodule.span_le]
    rintro _ ⟨y, _, rfl⟩
    obtain ⟨a0, a1, hq⟩ := hsp (Ideal.Quotient.mk (IE (E := E) v) y)
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective a0
    obtain ⟨b1, rfl⟩ := Ideal.Quotient.mk_surjective a1
    have e0 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b0) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b0) := rfl
    have e1 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b1) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b1) := rfl
    have hw : y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ ∈ IE (E := E) v := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, map_mul, hq, e0, e1]
      ring
    have hy : ι y = ((⟨iO v b0, mem_O_iO v b0⟩ : v.adicCompletionIntegers F) • (1 : Fv F v ⊗[F] E) +
        (⟨iO v b1, mem_O_iO v b1⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (θ : E)) +
        ι (1 * (y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ)) := by
      rw [ov_smul, ov_smul, mul_one]
      show _ = sc (E := E) v (iO v b0) + sc (E := E) v (iO v b1) * ι θ + _
      rw [← halg, ← halg, ← map_mul, ← map_add, ← map_add]
      congr 1
      ring
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩) (hI _ hw 1)
  have hle : Nt ≤ M := Submodule.le_of_le_smul_of_le_jacobson_bot
    (Submodule.fg_span ((Set.finite_range _).image _)) (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNM
  have hx' : x ∈ Submodule.span (v.adicCompletionIntegers F) (ι '' Set.univ) := hx
  have hxM : x ∈ M := by
    apply hle
    refine (Submodule.span_le.mpr ?_) hx'
    rintro _ ⟨y, _, rfl⟩
    exact hN y
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxM
  refine ⟨a, b, ?_⟩
  rw [← hab, ov_smul, ov_smul, mul_one]

theorem resAlg_of_eta (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_span σ J ψ v (thetaSpan_holds σ J ψ v) hE

end PI.OmLocU.Red
