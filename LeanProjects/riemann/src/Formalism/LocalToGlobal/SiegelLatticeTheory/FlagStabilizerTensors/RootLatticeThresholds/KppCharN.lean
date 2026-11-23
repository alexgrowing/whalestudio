import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharB

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D) {kv : Σ k : Fin 2, D.nd.PlG k}

theorem level_mem_wB' (kv : Σ k : Fin 2, D.nd.PlG k) : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal :=
  g_mem_of_gk X (gk_mem X kv)

theorem psiK_ne {ε : 𝓞 X.B.I.E} (hε1 : ε - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) : psiK X ε hε ≠ 1 := by
  intro h1
  have hp := D.host.g_prime kv.1
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩

  have hm : ∀ m : ℕ, X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) = 1 := by
    intro m
    have h2 := congrArg (fun ψ : AddChar (ZMod (D.host.g kv.1)) ℂ => ψ (m : ZMod (D.host.g kv.1))) h1
    simp only [psiK_apply, AddChar.one_apply, ZMod.val_natCast] at h2
    rw [← psi_period X hε (m % D.host.g kv.1) (m / D.host.g kv.1), Nat.mod_add_div] at h2
    exact h2

  have hb : ∀ b : 𝓞 X.B.I.F, X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b : 𝓞 X.B.I.E) : X.B.I.E)))) = 1 := by
    intro b
    set bE : 𝓞 X.B.I.E := algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b
    obtain ⟨c, hc⟩ := int_surj X.B.I (wK X kv) hp (card_wK X kv) (Ideal.Quotient.mk _ bE)
    set m : ℕ := ((c : ZMod (D.host.g kv.1)).val : ℕ)
    have hbm : bE - (m : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
      have h1' : bE - (c : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
      have h2' : ((c : 𝓞 X.B.I.E) - (m : 𝓞 X.B.I.E)) ∈ (wK X kv).asIdeal := by
        have : ((c - (m : ℤ) : ℤ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
          rw [int_mem_iff X.B.I (wK X kv) hp (card_wK X kv), ← ZMod.intCast_eq_intCast_iff_dvd_sub]
          simp [m]
        simpa using this
      have := add_mem h1' h2'
      simpa using this
    have hall : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal →
        ε * (bE - (m : 𝓞 X.B.I.E)) ∈ P.asIdeal := by
      intro P hP
      by_cases hPw : P = wK X kv
      · rw [hPw]; exact Ideal.mul_mem_left _ _ hbm
      · exact Ideal.mul_mem_right _ _ (hεP P hP hPw)
    obtain ⟨c', hc'⟩ := mem_g_of_all X hall
    have e : iE X.B.I (ε * bE) = iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * iE X.B.I c' := by
      have : ε * bE = ε * (m : 𝓞 X.B.I.E) + ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c' := by rw [← hc']; ring
      rw [this]; simp [iE]
    have h3 := hm m
    rw [← psi_modg X _ (iE_int X.B.I c'), ← e] at h3
    have e2 : iE X.B.I (ε * bE) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((ε : X.B.I.E) * (bE : X.B.I.E)) := by
      simp [iE]
    rw [e2, divN_incl] at h3
    exact h3

  set τ := PI.ScPsiExists.UnitaryGroupMassFormula.tau X.B.I.cm.fixed
  set y : X.B.I.F := (((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E)
  have htr : ∀ z : 𝓞 X.B.I.F, ∃ n : ℤ, Algebra.trace ℚ X.B.I.F (y * algebraMap (𝓞 X.B.I.F) X.B.I.F z) = n := by
    intro z
    have h4 := X.psiEf_rat (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) *
      ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E)))
    rw [hb z, one_mul] at h4
    obtain ⟨n, hn⟩ := PsiCondAllPf.trace_of_psi X.B.I _ h4
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    have hz : ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z) := rfl
    have e3 : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z)) =
        (((X.B.g : ℕ) : X.B.I.F)⁻¹ * algebraMap (𝓞 X.B.I.F) X.B.I.F z) • (ε : X.B.I.E) := by
      rw [Algebra.smul_def, map_mul, map_inv₀, map_natCast]; ring
    rw [hz, e3, LinearMap.map_smul, smul_eq_mul]
    ring

  let v : HeightOneSpectrum (𝓞 X.B.I.F) :=
    { asIdeal := (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have h5 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) := by
          rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
        rw [hbot] at h5
        exact (by exact_mod_cast hp.ne_zero : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ≠ 0) ((Submodule.mem_bot _).1 h5) }
  have hv : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
    exact PsiCondAllPf.unram_of (D.host.g kv.1) hp v hv
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split kv.1) v hv).1
  obtain ⟨d, hd, hdv⟩ := PsiCondAllPf.exists_diff_not_mem v hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int y htr d hd
  obtain ⟨t, ht⟩ := PI.ScPsiExists.UnitaryGroupMassFormula.tau_int X.B.I.cm.fixed ε

  have hgc : ((X.B.g : ℕ) : 𝓞 X.B.I.F) * c = t * d := by
    apply FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) X.B.I.F
    have hg0 : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
    rw [map_mul, map_mul, hc, ht, map_natCast]
    show (X.B.g : X.B.I.F) * ((((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E) * _) = τ (algebraMap (𝓞 X.B.I.E) X.B.I.E ε) * _
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
  have htd : t * d ∈ v.asIdeal := by
    rw [← hgc]
    refine Ideal.mul_mem_right _ _ ?_
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact g_mem_of_gk X (gk_mem X kv)
  have htv : t ∈ v.asIdeal := (v.isPrime.mem_or_mem htd).resolve_right hdv

  have htw : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t ∈ (wK X kv).asIdeal := htv
  have hte : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t = ε + sigO X.B.I ε := by
    apply RingOfIntegers.ext
    show algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F t) = (ε : X.B.I.E) + star (ε : X.B.I.E)
    rw [ht, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply]
  have hsig : sigO X.B.I ε ∈ (wK X kv).asIdeal := by
    have : ε ∈ (wc X.B.I (wK X kv)).asIdeal :=
      hεP _ (natCast_mem_wc X.B.I (level_mem_wB' X kv)) (wK_ne_wc X kv kv).symm
    rwa [mem_wc] at this
  rw [hte] at htw
  have h1w : (1 : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
    have := sub_mem (sub_mem htw hε1) hsig
    convert this using 1; ring
  exact (wK X kv).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1w)

end Formalism.L2.SG.Pf.KppChar
