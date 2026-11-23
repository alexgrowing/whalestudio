import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiFixAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix

namespace UpperTheory.V.Z.Kato.Joint

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem sm_sys {W : R2 Ω l} {c : Coef l} {y : G ℚ Ω → Fin 2 → Qbar l} {S' : Finset Pl} (h : Sys W c y S')
    {a : Qbar l} (ha : a ∈ c.O) : Sys W c (fun s => a • y s) S' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, Submodule.smul_mem _ a h2, fun s i => c.O.mul_mem ha (h3 s i), fun w hw => ?_, fun n hn w hw hd ψ hk hs => ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := h4 w hw
    refine ⟨B, hB, a • x, fun s hs => ?_⟩
    simp only [hx s hs, Matrix.mulVec_smul, smul_sub]
  · obtain ⟨Y, P, u, b, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := h5 n hn w hw hd ψ hk hs
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, fun s x i => c.O.mul_mem ha (k2 s x i), k3, k4,
      fun i => c.O.mul_mem ha (k5 i), fun s t x => ?_, fun s => ?_, k8, fun q hq hl => ?_⟩
    · exact k1.const_smul a
    · simp only [k6, Matrix.mulVec_smul, smul_add]
    · have := k7 s
      rw [finsum_eq_sum_of_fintype] at this ⊢
      rw [← Finset.smul_sum, this]
      simp only [Matrix.mulVec_smul, smul_add, smul_sub, smul_comm a P]
    · obtain ⟨B, hB, t, ht, ht'⟩ := k9 q hq hl
      refine ⟨B, hB, fun x => a • t x, fun x i => c.O.mul_mem ha (ht x i), fun s hs x => ?_⟩
      simp only [ht' s hs, Matrix.mulVec_smul, smul_sub]

private theorem sm_iw {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (h : IwSys2 c A ν Z) (d : ℕ) (hd : Nat.Coprime d l) :
    IwSys2 c A ν (smZ d hd Z) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun r => ⟨fun s x => ?_, fun s hs t ht x => ?_⟩, fun r s x => ?_⟩
  · exact c.O.sub_mem ((h2 r).1 _ _) (c.O.mul_mem (natCast_mem c.O d) ((h2 r).1 _ _))
  · unfold smZ
    rw [(h2 r).2 s hs t ht, (h2 r).2 s hs t ht, mul_right_comm x]
    ring
  · unfold smZ
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← h3 r s x, h3 r s (x * _)]
    congr 2
    have hu : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom
        (ZMod.unitOfCoprime d (Nat.Coprime.pow_right (r + 1) hd)) = ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) := by
      ext
      simp only [Units.coe_map, ZMod.coe_unitOfCoprime, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_natCast]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (ZMod.unitOfCoprime d (Nat.Coprime.pow_right (r + 1) hd))) (fun i => ?_)
      (fun i _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight, map_mul, hu, mul_left_inj]

private theorem sm_norm_nat {a : ℕ} (h : Nat.Coprime a l) : ‖(a : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

private theorem sm_eta {r n : ℕ} (hr : 1 ≤ r) (hn : n ≤ r) (e : ℕ) (ψ : ZMod l → Qbar l) (hψ : ∀ x, ‖ψ x‖ ≤ 1)
    (d : ℕ) (hd : Nat.Coprime d l) (hd1 : (d : ZMod l) = 1) (x : (ZMod (l ^ r))ˣ) :
    ‖((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x - (d : Qbar l) ^ e *
      ((((((x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ *
        chiK l ψ r (x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd)))‖ ≤ ‖(l : Qbar l) ^ n‖ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  unfold chiK
  set z := x * ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) with hz
  have hmod : (z : ZMod (l ^ r)).val ≡ (x : ZMod (l ^ r)).val * d [MOD l ^ r] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hz, Units.val_mul,
      ZMod.coe_unitOfCoprime]
  have hl : l ∣ l ^ r := dvd_pow_self l (by omega)
  have ha := sm_norm_nat (Nat.Coprime.coprime_dvd_right hl (ZMod.val_coe_unit_coprime x))
  have hb := sm_norm_nat (Nat.Coprime.coprime_dvd_right hl (ZMod.val_coe_unit_coprime z))
  generalize (z : ZMod (l ^ r)).val = b at *
  generalize (x : ZMod (l ^ r)).val = a at *
  have hψe : ((b : ℕ) : ZMod l) = ((a : ℕ) : ZMod l) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod.of_dvd hl), Nat.cast_mul, hd1, mul_one]
  obtain ⟨k, hk⟩ := ((hmod.of_dvd (pow_dvd_pow l hn)).pow e).symm.dvd
  have hk' : (b : Qbar l) ^ e - ((a : Qbar l) * d) ^ e = (l : Qbar l) ^ n * k := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) hk
  have ha0 : (a : Qbar l) ≠ 0 := by rw [← norm_ne_zero_iff, ha]; exact one_ne_zero
  have hb0 : (b : Qbar l) ≠ 0 := by rw [← norm_ne_zero_iff, hb]; exact one_ne_zero
  have key : ((a : Qbar l) ^ e)⁻¹ * ψ a - (d : Qbar l) ^ e * (((b : Qbar l) ^ e)⁻¹ * ψ b) =
      (l : Qbar l) ^ n * (k * ψ a) * (((a : Qbar l) ^ e)⁻¹ * ((b : Qbar l) ^ e)⁻¹) := by
    rw [hψe, ← mul_assoc ((l : Qbar l) ^ n), ← hk', mul_pow]
    field_simp
  rw [key, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow (a : Qbar l), norm_pow (b : Qbar l), ha, hb]
  simp only [one_pow, inv_one, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ k) (norm_nonneg _) (hψ _))

private theorem sm_sp {c : Coef l} {A : ValuationSubring Ω}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hZ : ∀ r s x, Z r s x ∈ c.O) (e : ℕ) (ψ : ZMod l → Qbar l)
    (hψ : ∀ x, ‖ψ x‖ ≤ 1) (d : ℕ) (hd : Nat.Coprime d l) (hd1 : (d : ZMod l) = 1) {y : G ℚ Ω → Fin 2 → Qbar l}
    (h : SpLink A e (chiK l ψ) Z y) :
    SpLink A e (chiK l ψ) (smZ d hd Z) fun s => (1 - (d : Qbar l) ^ (e + 1)) • y s := by
  intro n
  obtain ⟨r₀, hr₀⟩ := h n
  refine ⟨max r₀ (max n 1), fun r hr s hs hc => ?_⟩
  have h0 := hr₀ r (by omega) s hs hc
  have h1 := sm_eta (r := r) (n := n) (by omega) (by omega) e ψ hψ d hd hd1
  unfold Cg at h0 ⊢
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  set u := ZMod.unitOfCoprime d (Nat.Coprime.pow_right r hd) with hu
  have h2 : ∀ x, ‖η x - (d : Qbar l) ^ e * η (x * u)‖ ≤ ‖(l : Qbar l) ^ n‖ := h1
  have hsp : sp η (Z r) s = ∑ x, η (x * u) * Z r s (x * u) :=
    (Fintype.sum_equiv (Equiv.mulRight u) _ _ fun x => rfl).symm
  have hsm : sp η (smZ d hd Z r) s = sp η (Z r) s - d * ∑ x, η x * Z r s (x * u) := by
    unfold sp smZ
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [← hu]; ring
  have hD : ∑ x, (η x - (d : Qbar l) ^ e * η (x * u)) * Z r s (x * u) =
      ∑ x, η x * Z r s (x * u) - (d : Qbar l) ^ e * sp η (Z r) s := by
    rw [hsp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have key : ((1 - (d : Qbar l) ^ (e + 1)) • y s) 1 - sp η (smZ d hd Z r) s =
      (1 - (d : Qbar l) ^ (e + 1)) * (y s 1 - sp η (Z r) s) +
        d * ∑ x, (η x - (d : Qbar l) ^ e * η (x * u)) * Z r s (x * u) := by
    rw [hD, hsm, Pi.smul_apply, smul_eq_mul]
    ring
  have hc1 : ‖(1 - (d : Qbar l) ^ (e + 1))‖ ≤ 1 :=
    GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c.O.sub_mem c.O.one_mem (c.O.pow_mem (natCast_mem c.O d) _))
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans h0
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (sm_norm_nat hd).le).trans ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hZ _ _ _))).trans (h2 x)

end UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.smSys : UpperTheory.V.Z.Kato.Joint.SmSys := by
  intro l _ Ω _ _ W c y S' A ν Z e ψ d hd hd1 hψ h1 h2 h3
  exact ⟨sm_sys h1 (c.O.sub_mem c.O.one_mem (c.O.pow_mem (natCast_mem c.O d) _)), sm_iw h2 d hd,
    sm_sp (fun r => (h2.2.1 r).1) e ψ hψ d hd hd1 h3⟩

end
