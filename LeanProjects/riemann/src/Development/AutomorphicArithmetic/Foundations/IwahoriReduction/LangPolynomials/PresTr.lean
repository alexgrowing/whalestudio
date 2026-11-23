import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Pointwise

private theorem pt_pv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (b : ℕ) (hz : τ z = z ^ b) :
    pv (Polynomial.expand (R0 A) b P) z = τ (pv P z) := by
  unfold pv
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow, ← hz]
  have hc : ((τ : Ω →+* Ω)).comp (R0 A).subtype = (R0 A).subtype := by
    ext r
    exact r.2.2 τ hτ
  have e : (τ : Ω →+* Ω) (Polynomial.eval₂ (R0 A).subtype z P)
      = Polynomial.eval₂ (R0 A).subtype ((τ : Ω →+* Ω) z) P := by
    rw [Polynomial.hom_eval₂, hc]
  exact e.symm

private theorem pt_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) {x : Ω} (hx : x ∈ A) : τ x ∈ A := by
  have h := mem_Dec.mp (Ine_le_Dec A hτ)
  have h2 := ValuationSubring.smul_mem_pointwise_smul τ x A hx
  rw [h] at h2
  exact h2

private theorem pt_cg {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Type} [Fintype ι] (o : ι → Qbar l) (ho : ∀ i, ‖o i‖ ≤ 1)
    (k : ι → ZMod (l ^ n)) (b : ℕ) (x : Qbar l) (h : Cg n x (∑ i, o i * ((k i).val : Qbar l))) :
    Cg n ((b : Qbar l) * x) (∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)) := by
  unfold Cg at h ⊢
  haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
  have hc : ∀ i, (((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l))
      = (b : Qbar l) * ((k i).val : Qbar l) - (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
    intro i
    have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
      rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h3 : ((b * (k i).val : ℕ) : Qbar l) = (((b * (k i).val) % l ^ n : ℕ) : Qbar l)
        + (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [Nat.cast_mul] at h3
    linear_combination -h3
  have hs : ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = ∑ i, (b : Qbar l) * (o i * ((k i).val : Qbar l))
        - ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hc]; ring)
  have key : (b : Qbar l) * x - ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = (b : Qbar l) * (x - ∑ i, o i * ((k i).val : Qbar l))
        + ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [hs, mul_sub, Finset.mul_sum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : Qbar l)‖ * ‖x - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ 1 * ‖(l : Qbar l) ^ n‖ :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) h (norm_nonneg _) zero_le_one
      _ = ‖(l : Qbar l) ^ n‖ := one_mul _
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => ?_)
    rw [norm_mul, norm_mul]
    calc ‖o i‖ * (‖(l : Qbar l) ^ n‖ * ‖(((b * (k i).val) / l ^ n : ℕ) : Qbar l)‖)
        ≤ 1 * (‖(l : Qbar l) ^ n‖ * 1) := by
          gcongr
          · exact ho i
          · exact IsUltrametricDist.norm_natCast_le_one _ _
      _ = ‖(l : Qbar l) ^ n‖ := by ring

theorem UpperTheory.Kd.C7.pPresTr :
    UpperTheory.Kd.C7.SPresTr := by
  intro l _ hl Ω _ _ _ A hOver c β ζ hR Z hI b hb m n P hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hbu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hb ?_)
    have h' : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h')
  obtain ⟨τ, hτ, hτc⟩ := (pFrobEx l hl Ω A hOver).2.2 hbu.unit
  have hmodpow : ∀ (t : Ω) (N a : ℕ), t ^ N = 1 → t ^ a = t ^ (a % N) := by
    intro t N a ht
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, ht, one_pow, mul_one]
  have hτpow : ∀ (t : Ω) (r : ℕ), t ^ l ^ r = 1 → τ t = t ^ b := by
    intro t r ht
    have hs := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) t ht
    have e1 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) = hbu.unit := hτc
    rw [e1, IsUnit.unit_spec, map_natCast, ZMod.val_natCast] at hs
    rw [hmodpow t (l ^ r) b ht]
    exact hs
  have hcyc : cycMod ℚ Ω l m τ = un b hb m := by
    apply Units.ext
    show (PadicInt.toZModPow m) ((cycZ ℚ Ω l τ : ℤ_[l])) = _
    rw [hτc, IsUnit.unit_spec, map_natCast]
    simp [un]
  have hu' : ∀ i, pv (Polynomial.expand (R0 A) b (P i)) (ζ m) = τ (pv (P i) (ζ m)) := fun i =>
    pt_pv hτ (P i) (ζ m) b (hτpow (ζ m) m (hR m).1.pow_eq_one)
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hnorm, hmain⟩ := hB
  refine ⟨hprim, hnm, fun i => ?_, hnorm, ?_⟩
  · dsimp only
    rw [hu' i]
    obtain ⟨h1, h2, h3⟩ := hunits i
    refine ⟨pt_mem hτ h1, (map_ne_zero τ).mpr h2, ?_⟩
    rw [← map_inv₀]
    exact pt_mem hτ h3
  · intro s hs hcs hsz
    have hs' : τ⁻¹ * s * τ ∈ Ine A := mul_mem (mul_mem (inv_mem hτ) hs) hτ
    have hcs' : cycMod ℚ Ω l m (τ⁻¹ * s * τ) = 1 := by simp [hcs]
    have hsz' : (τ⁻¹ * s * τ) (ζ n) = ζ n := fix_of_cycMod hnm hcs' hprim.pow_eq_one
    obtain ⟨k, hk, hcg⟩ := hmain _ hs' hcs' hsz'
    haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
    refine ⟨fun i => (b : ZMod (l ^ n)) * k i, fun i => ?_, ?_⟩
    · obtain ⟨v, hv1, hv2⟩ := hk i
      refine ⟨τ v, ?_, ?_⟩
      · show (τ v) ^ l ^ n = pv (Polynomial.expand (R0 A) b (P i)) (ζ m)
        rw [hu' i, ← map_pow, hv1]
      · have e2 : s (τ v) = τ ((τ⁻¹ * s * τ) v) := by
          rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
          rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
          congr 1
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [e2, hv2, map_mul, map_pow, hτpow (ζ n) n hprim.pow_eq_one, ← pow_mul, h1,
          ← hmodpow (ζ n) (l ^ n) _ hprim.pow_eq_one]
    · have hHm : τ⁻¹ * s * τ ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs', hcs'⟩
      have hC := (pConj l hl Ω A hOver c Z hI m _ hHm τ hτ).2 (un b hb m)
      have e3 : τ * (τ⁻¹ * s * τ) * τ⁻¹ = s := by group
      rw [e3, hcyc, mul_inv_cancel] at hC
      show Cg n ((b : Qbar l) * Z m s (1 * un b hb m)) _
      rw [one_mul, hC]
      exact pt_cg β.val hnorm k b _ hcg
