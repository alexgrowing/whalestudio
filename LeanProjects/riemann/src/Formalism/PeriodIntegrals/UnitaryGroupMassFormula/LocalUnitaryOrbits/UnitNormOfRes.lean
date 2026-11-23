import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsPerpNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
  PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem tr_nd_field {k K : Type} [Field k] [Field K] [Algebra k K] (σ' : K ≃ₐ[k] K) (hne : σ' ≠ AlgEquiv.refl)
    (z : K) (hz : z ≠ 0) : ∃ t : K, t * z + σ' (t * z) ≠ 0 := by
  have hu : ∃ u : K, u + σ' u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have h1 : (1 : K) + 1 = 0 := by simpa using h 1
    ext u
    have h2 : σ' u = -u := eq_neg_of_add_eq_zero_right (h u)
    rw [h2]
    show -u = u
    have h3 : u + u = 0 := by rw [← mul_one u, ← mul_add, h1, mul_zero]
    exact (eq_neg_of_add_eq_zero_left h3).symm
  obtain ⟨u, hu⟩ := hu
  refine ⟨u * z⁻¹, ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  exact hu

theorem tr_nd_prod {k : Type} [Field k] (z : k × k) (hz : z ≠ 0) :
    ∃ t : k × k, t * z + (RingEquiv.prodComm (R := k) (S := k)).toRingHom (t * z) ≠ 0 := by
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by
      intro h2
      exact hz (Prod.ext h1 h2)
    refine ⟨(0, z.2⁻¹), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h2] at this
  · refine ⟨(z.1⁻¹, 0), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h1] at this

theorem trNd_of_res {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hcm : IsCMExt F E σ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (hres : IsRes σ v ϖ τ π) (hnd : ∀ z : K, z ≠ 0 → ∃ t : K, t * z + τ (t * z) ≠ 0)
    (c : Fv F v ⊗[F] E) (hc : c ∈ OEv (E := E) v) (hcn : sc (E := E) v (ϖ⁻¹) * c ∉ OEv (E := E) v) :
    ∃ t ∈ OEv (E := E) v, IsU v (t * c + sigR (Fv F v) σ (t * c)) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨hsurj, hker, hsig⟩ := hres
  let cO : OR (E := E) v := ⟨c, hc⟩
  have hc0 : π cO ≠ 0 := by
    intro h
    obtain ⟨d, hd0, hd⟩ := (hker cO).1 h
    apply hcn
    have hd' : c = sc (E := E) v ϖ * d := hd
    rw [hd', ← mul_assoc, sc_eq, sc_eq, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul]
    exact hd0
  obtain ⟨tb, htb⟩ := hnd _ hc0
  obtain ⟨tO, htO⟩ := hsurj tb
  have ht0 : (tO : Fv F v ⊗[F] E) ∈ OEv (E := E) v := tO.2
  have htc0 : (tO : Fv F v ⊗[F] E) * c ∈ OEv (E := E) v := (tO * cO).2
  let yO : OR (E := E) v := ⟨sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c), sigR_mem σ v htc0⟩
  have hy : π yO = τ (π (tO * cO)) := hsig (tO * cO) yO rfl
  set s := (tO : Fv F v ⊗[F] E) * c + sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c) with hs
  have hsO : π (tO * cO + yO) ≠ 0 := by
    rw [map_add, hy, map_mul, htO]
    exact htb
  have hs0 : s ∈ OEv (E := E) v := (tO * cO + yO).2
  have hsf : sigR (Fv F v) σ s = s := by
    rw [hs, map_add, sigR_invol σ v hcm, add_comm]
  refine ⟨tO, ht0, ?_⟩
  obtain ⟨a, ha, hsa⟩ := fix_int σ v hcm hs0 hsf
  rw [← hs, hsa]
  by_cases hva : Valued.v a < 1
  · exfalso
    obtain ⟨d, hd⟩ := (mem_unifO_iff v hϖ ⟨a, ha⟩).2 hva
    apply hsO
    apply (hker _).2
    refine ⟨sc (E := E) v (d : Fv F v), sc_mem v d.2, ?_⟩
    show s = _
    rw [hsa, sc_eq, sc_eq, sc_eq, ← map_mul]
    exact congrArg _ hd
  · have ha1 : Valued.v a = 1 := le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 ha) (not_lt.1 hva)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact zero_ne_one ha1
    have hai : a⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha1, inv_one]
    refine ⟨sc (E := E) v (a⁻¹), sc_mem v hai, ?_⟩
    rw [sc_eq, sc_eq, ← map_mul, mul_inv_cancel₀ ha0, map_one]

theorem trNd_of (hR : ResAlg σ J ψ v) : TrNd σ J ψ v := by
  intro hstd hun ϖ hϖ c hc hcn
  obtain ⟨k, _, _, -, hcase⟩ := hR hstd hun ϖ hϖ
  rcases hcase with ⟨-, K, _, _, σ', π, -, -, hne, hres⟩ | ⟨-, π, hres⟩
  · exact trNd_of_res σ v (σ' : K →+* K) π hstd.1 hϖ hres (fun z hz => tr_nd_field σ' hne z hz) c hc hcn
  · exact trNd_of_res σ v _ π hstd.1 hϖ hres (fun z hz => tr_nd_prod z hz) c hc hcn

theorem unitNorm_of_res (hR : ResAlg σ J ψ v) : UnitNorm σ J ψ v Λ :=
  unitNorm_of σ J ψ v Λ (fixLoc_holds σ v) (trNd_of σ J ψ v hR) (primPerp_holds σ J ψ v Λ)

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v) (hR : ResAlg σ J ψ v) :
    OrbAll σ J ψ v Λ a Y :=
  orbAll_of_norm σ J ψ v Λ a Y hN (unitNorm_of_res σ J ψ v Λ hR)

end PI.OmLocU.UnN
