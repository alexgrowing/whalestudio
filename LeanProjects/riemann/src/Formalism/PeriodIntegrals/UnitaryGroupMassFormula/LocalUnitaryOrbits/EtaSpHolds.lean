import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfEtaSp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GenOfTwo

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem two_primes (e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)) :
    ∃ Q Q' : Ideal (𝓞 E), Q.IsMaximal ∧ Q'.IsMaximal ∧ Q ≠ Q' ∧ Q.LiesOver v.asIdeal ∧ Q'.LiesOver v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let g : 𝓞 E →+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) :=
    e.toRingHom.comp (Ideal.Quotient.mk (IE (E := E) v))
  have hg : Function.Surjective g := e.surjective.comp Ideal.Quotient.mk_surjective
  have hIE : ∀ c ∈ v.asIdeal, g (algebraMap (𝓞 F) (𝓞 E) c) = 0 := by
    intro c hc
    simp only [g, RingHom.comp_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hc), map_zero]
  have key : ∀ f : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) →+* 𝓞 F ⧸ v.asIdeal, Function.Surjective f →
      (RingHom.ker (f.comp g)).IsMaximal ∧ (RingHom.ker (f.comp g)).LiesOver v.asIdeal := by
    intro f hf
    have hM : (RingHom.ker (f.comp g)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hf.comp hg)
    refine ⟨hM, ⟨?_⟩⟩
    have hle : v.asIdeal ≤ (RingHom.ker (f.comp g)).under (𝓞 F) := by
      intro c hc
      rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hIE c hc, map_zero]
    exact v.isMaximal.eq_of_le (by rw [Ideal.under_def]; exact Ideal.comap_ne_top _ hM.ne_top) hle
  obtain ⟨h1, h1'⟩ := key (RingHom.fst _ _) Prod.fst_surjective
  obtain ⟨h2, h2'⟩ := key (RingHom.snd _ _) Prod.snd_surjective
  refine ⟨_, _, h1, h2, ?_, h1', h2'⟩
  obtain ⟨y, hy⟩ := hg (1, 0)
  intro heq
  have hy2 : y ∈ RingHom.ker ((RingHom.snd _ _).comp g) := by
    rw [RingHom.mem_ker, RingHom.comp_apply, hy]
    rfl
  rw [← heq, RingHom.mem_ker, RingHom.comp_apply, hy] at hy2
  exact one_ne_zero hy2

theorem etaSp_holds : EtaSp σ J ψ v := by
  intro hstd hun hp
  have hcm := hstd.1
  obtain ⟨e, -⟩ := qProd_holds σ J ψ v hstd hun hp
  obtain ⟨Q, Q', hQ, hQ', hne, hl, hl'⟩ := two_primes v e
  obtain ⟨φ⟩ := MassDataIdxEmb.emb_of_two hcm.2.2.1 v Q Q' hne
  obtain ⟨θ, h3, -⟩ := theta_exists (σ := σ) (v := v) hcm
  have hind := theta_indep (σ := σ) (v := v) hcm θ h3
  set A := algebraMap (Fv F v) (Fv F v ⊗[F] E) with hA
  set T := inclR (F := F) (Fv F v) (θ : E) with hT
  have hind' : ∀ a0 a1 : Fv F v, A a0 + A a1 * T = 0 → a1 = 0 := fun a0 a1 h =>
    (hind a0 a1 (by rw [sc_eq', sc_eq']; exact h)).2
  have hnotF : ∀ c : F, algebraMap F E c ≠ (θ : E) := by
    intro c hc
    have h0 := hind' (-(algebraMap F (Fv F v) c)) 1 (by
      rw [map_neg, map_one, one_mul, hT, ← hc, inclR_alg', sc_eq', neg_add_cancel])
    exact one_ne_zero h0
  obtain ⟨t, ht⟩ := fix_range σ hcm (y := (θ : E) + σ θ) (by rw [map_add, sig_sig σ hcm, add_comm])
  obtain ⟨m, hm⟩ := fix_range σ hcm (y := (θ : E) * σ θ) (by rw [map_mul, sig_sig σ hcm, mul_comm])
  set r := φ (θ : E) with hr
  set r' := φ (σ (θ : E)) with hr'
  have hsum : A r + A r' = inclR (F := F) (Fv F v) ((θ : E) + σ θ) := by
    rw [← ht, inclR_alg', sc_eq', ← φ.commutes t, ht, map_add, map_add]
  have hprod : A r * A r' = inclR (F := F) (Fv F v) ((θ : E) * σ θ) := by
    rw [← hm, inclR_alg', sc_eq', ← φ.commutes m, hm, map_mul, map_mul]
  have hkey : (T - A r) * (T - A r') = 0 := by
    calc (T - A r) * (T - A r') = T * T - (A r + A r') * T + A r * A r' := by ring
      _ = inclR (F := F) (Fv F v) ((θ : E) * θ - ((θ : E) + σ θ) * θ + θ * σ θ) := by
          rw [hsum, hprod, hT]
          simp only [map_add, map_sub, map_mul]
      _ = 0 := by rw [show (θ : E) * θ - ((θ : E) + σ θ) * θ + θ * σ θ = 0 by ring, map_zero]
  set d := r - r' with hd
  have hd0 : d ≠ 0 := by
    intro h
    have h' : (θ : E) = σ θ := RingHom.injective φ.toRingHom (sub_eq_zero.1 h)
    obtain ⟨c, hc⟩ := fix_range σ hcm (y := (θ : E)) h'.symm
    exact hnotF c hc
  have hsq : (T - A r') * (T - A r') = A d * (T - A r') := by
    have h1 : (T - A r') * (T - A r') = (T - A r) * (T - A r') + (A r - A r') * (T - A r') := by ring
    rw [h1, hkey, zero_add, ← map_sub]
  have hinv : A d⁻¹ * A d = 1 := by rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
  have hdi : d⁻¹ ≠ 0 := inv_ne_zero hd0
  refine ⟨A d⁻¹ * (T - A r'), ?_, ?_, ?_⟩
  · calc A d⁻¹ * (T - A r') * (A d⁻¹ * (T - A r')) = A d⁻¹ * A d⁻¹ * ((T - A r') * (T - A r')) := by ring
      _ = A d⁻¹ * (T - A r') * (A d⁻¹ * A d) := by rw [hsq]; ring
      _ = A d⁻¹ * (T - A r') := by rw [hinv, mul_one]
  · intro h
    exact hdi (hind' (-(d⁻¹ * r')) d⁻¹ (by rw [map_neg, map_mul]; linear_combination h))
  · intro h
    exact hdi (hind' (-(d⁻¹ * r') - 1) d⁻¹ (by rw [map_sub, map_neg, map_mul, map_one]; linear_combination h))

end PI.OmLocU.Red
