import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CountVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HostNumberS

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
private theorem arith {a V E : ℕ} {s L X : ℝ} {C : ℕ} (ha : a ≤ V) (hV : (V : ℝ) ≤ 2 * E * s) (hL : 0 ≤ L)
    (hs : s * L ≤ X ^ C) (hX : 2 ≤ X) : (a : ℝ) / E * L ≤ X ^ (C + 1) := by
  have hp : 0 ≤ X ^ C := pow_nonneg (by linarith) C
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg (by linarith) _
  · have hE' : (0 : ℝ) < E := by exact_mod_cast hE
    have ha' : (a : ℝ) ≤ V := by exact_mod_cast ha
    have h1 : (a : ℝ) / E ≤ 2 * s := by
      rw [div_le_iff₀ hE']
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL
    have h3 := mul_le_mul_of_nonneg_left hX hp
    rw [pow_succ]
    linarith
private theorem l_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  have h : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have := map_nonunit (algebraMap ℤ_[l] c.O) _ h
  rwa [map_natCast] at this
theorem UpperTheory.V.UnitaryThreeInertia.countV_of_finiteness_duality_euler_host :
    _root_.UpperTheory.V.Aut.ThmS6_s → LemmaM → LemmaM' → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → GlobalTheory.Published.PoitouTateNormalised → HostVanE → HostXpp → _root_.UpperTheory.V.UnitaryThreeInertia.HostRigid_s → _root_.UpperTheory.V.UnitaryThreeInertia.HostNumber_s → CountV := by
  intro hS6 hM hM' hLF hLT hLE hGF hGE hPT hVan hX hRig hNum χ
  obtain ⟨K, _, _, _, hK⟩ := gaussian_field_range_eq_ker_quartic_char.1
  obtain ⟨C, hC⟩ := hNum K hK
  refine ⟨C + 1, fun h _ t _ Ω _ _ _ l hl c e h2 he _ ψ hψ hP => ?_⟩
  obtain ⟨hD, hXD⟩ := hostData_of_host h c e h2 he ψ hψ hP.2
  obtain ⟨S, A, F, hF⟩ := exists_hostFrame Ω c e ψ _ hD
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨g₁, hg, hS⟩ := hS6 K hK Ω l ι c h.N e ψ _ hD S A F hF
  obtain ⟨hphi, i1, i2, i3, i4, i5, i6⟩ := hostFrame_phi hGF Ω c e ψ _ hD S A F hF
  have hOk := hostFrame_ok Ω c e ψ _ hD S A F hF
  obtain ⟨R, _, _, _, u, hu⟩ := exists_isUniv F hOk l hl.out (l_mem c) hphi g₁ hg
  obtain ⟨hfin, hB⟩ := hS R u hu
  obtain ⟨φ, hne, hsum⟩ := hC Ω l c h.N e ψ _ hD S A F hF ι g₁ hg
  obtain ⟨n, r, V, hr, hinj, hV, hle⟩ := abstract_count hM hM' (l := l) F hOk
    (hostFrame_locVan hLF hLT hLE Ω c e ψ _ hD S A F hF)
    (hostFrame_count hLF hLT hLE hGF hGE hPT Ω c e ψ _ hD S A F hF)
    (hVan Ω l c h.N e ψ _ hD S A F hF) (frame_class_one Ω c e ψ _ hD S A F hF)
    (hX Ω l c h.N e ψ _ hD _ hXD S A F hF) g₁ hg u hu hfin φ
    (fun r => _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) hB
    (fun r h1 h2 h3 => ⟨hRig K hK Ω l c h.N e ψ _ hD S A F hF ι g₁ hg r h1 h3, hne r h1 h2 h3⟩)
  have hlen := vlen_le Ω c e ψ _ hD S A F hF V hV
  have hX2 : (2 : ℝ) ≤ (l : ℝ) * h.N * e := by
    have : 2 * 1 * 1 ≤ l * h.N * e := Nat.mul_le_mul (Nat.mul_le_mul hl.out.two_le h.N_pos) he
    exact_mod_cast this
  refine ⟨ne_top_of_le_ne_top (ENat.coe_ne_top V) hlen, ?_⟩
  exact arith (ENat.toNat_le_of_le_coe hlen) hle (Real.log_natCast_nonneg l) (hsum n r hr hinj) hX2
end
