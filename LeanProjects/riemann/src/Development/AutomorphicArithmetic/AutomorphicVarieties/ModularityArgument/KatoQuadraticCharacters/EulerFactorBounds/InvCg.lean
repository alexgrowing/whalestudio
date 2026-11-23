import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem sadd {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖a + b‖ ≤ δ :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem smul' {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ δ) : ‖a * b‖ ≤ δ := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

private theorem shift {l : ℕ} [Fact l.Prime] {U : Type} [CommGroup U] [Fintype U] {δ : ℝ} (hδ : 0 ≤ δ) (η F : U → Qbar l) (t : U)
    (c : Qbar l) (h : ∀ y, ‖η (y * t) - η y * c‖ ≤ δ) (hF : ∀ y, ‖F y‖ ≤ 1) :
    ‖∑ y, η y * F (y * t⁻¹) - c * ∑ y, η y * F y‖ ≤ δ := by
  have e : ∑ y, η y * F (y * t⁻¹) = ∑ y, η (y * t) * F y :=
    (Fintype.sum_equiv (Equiv.mulRight t) _ _ fun y => by simp).symm
  rw [e, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun y _ => ?_
  have : η (y * t) * F y - c * (η y * F y) = F y * (η (y * t) - η y * c) := by ring
  rw [this]
  exact smul' (hF y) (h y)

private theorem unit_of {l r : ℕ} [hl : Fact l.Prime] (hr : r ≠ 0) (y : (ZMod (l ^ r))ˣ) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((y : ZMod (l ^ r)).val : ℕ) := by
  have h := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr) (ZMod.val_coe_unit_coprime y)
  have : IsUnit (((y : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact h.symm
  exact this

private theorem inv_cg {l r : ℕ} [hl : Fact l.Prime] (c : Coef l) (hr : r ≠ 0) (e : ℕ) (y t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ)
    (h : PadicInt.toZModPow r (τ : ℤ_[l]) = t) :
    ‖((((((y * t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ -
      (((((y : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ * ((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  obtain ⟨u, hu⟩ := unit_of hr (y * t)
  obtain ⟨v, hv⟩ := unit_of hr y
  have h1 : (l : ℤ_[l]) ^ r ∣ ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, Units.val_mul, map_mul, hu, hv, h,
      map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_mul, sub_self]
  obtain ⟨k, hk⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ e)
  have inv : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((w⁻¹ : ℤ_[l]ˣ) ^ e) := fun w => by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_pow, ← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one]
  rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← hu, ← hv,
    inv, inv, inv, ← map_mul, ← map_sub]
  have e1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e - ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e =
      (k * ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e) * (l : ℤ_[l]) ^ r := by
    have a1 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) ^ e = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
    have a2 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * (u : ℤ_[l]) ^ e =
        ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← mul_pow, ← Units.val_mul, ← Units.val_mul, mul_comm u⁻¹, inv_mul_cancel_right, mul_inv]
    rw [← a1, ← a2, ← mul_sub, hk]; ring
  rw [e1, map_mul, map_pow, map_natCast]
  exact smul' (nle c (c.O.algebraMap_mem _)) le_rfl

theorem UpperTheory.V.Z.Kato.Nb.sSpec :
    UpperTheory.V.Z.Kato.Nb.SSpec := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW p r hp hlp a δ k ha hδ hk Y V b hY hb H
  obtain ⟨hθ, h1, hmul, hψ, hρ, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hW
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨0, fun i => zero_mem _, fun s i => ?_⟩
    have z : ∀ y : (ZMod (l ^ 0))ˣ, (y : ZMod (l ^ 0)).val = 0 := fun y =>
      Nat.lt_one_iff.1 (by simpa using ZMod.val_lt (y : ZMod (l ^ 0)))
    simp only [Cg, spec, z, Nat.cast_zero, zero_pow (show e ≠ 0 by omega), inv_zero, zero_mul, zero_smul, Finset.sum_const_zero]
    simp
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  let rd : (ZMod (l ^ r))ˣ →* (ZMod l)ˣ := Units.map (ZMod.castHom (dvd_pow_self l hr) (ZMod l)).toMonoidHom
  have hrd : ∀ y, chiK l ψ r y = ψ (rd y : (ZMod l)ˣ) := fun y => by
    rw [chiK, ZMod.natCast_val]; rfl
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  have uO : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w)⁻¹ ∈ cf.O := fun w => by
    rw [show (algebraMap ℤ_[l] (Qbar l) w)⁻¹ = algebraMap ℤ_[l] (Qbar l) (w⁻¹ : ℤ_[l]ˣ) from
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])]
    exact cf.O.algebraMap_mem _
  have ηO : ∀ y, η y ∈ cf.O := fun y => by
    obtain ⟨u, hu⟩ := unit_of hr y
    simp only [hη]
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← inv_pow, hrd]
    exact mul_mem (pow_mem (uO u) e) (hψ _)
  have key : ∀ (t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ), PadicInt.toZModPow r (τ : ℤ_[l]) = t → ∀ y,
      ‖η (y * t) - η y * (((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹ * ψ (rd t : (ZMod l)ˣ))‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun t τ h y => by
    simp only [hη]
    rw [hrd, hrd, map_mul, hmul]
    have := smul' (nle cf (mul_mem (hψ (rd y)) (hψ (rd t)))) (inv_cg cf hr e y t τ h)
    convert this using 2
    ring
  have hp1 : (p : ZMod l) = 1 := by
    obtain ⟨m, hm⟩ := hlp
    rw [show p = l * m + 1 by have := hp.pos; omega]
    simp
  have hcop : Nat.Coprime l p := by
    rw [Nat.Prime.coprime_iff_not_dvd hl.out, ← ZMod.natCast_eq_zero_iff, hp1]
    exact one_ne_zero
  obtain ⟨π, hπ⟩ : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; exact hcop
  have hq : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hcop.symm.pow_right r)
  have hinv : inv1 (l ^ r) p = hq.unit⁻¹ := dif_pos hq
  have hπ' : algebraMap ℤ_[l] (Qbar l) π = p := by rw [hπ, map_natCast]
  have hrq : ((rd hq.unit : (ZMod l)ˣ) : ZMod l) = 1 := by
    rw [← hp1]; exact map_natCast (ZMod.castHom (dvd_pow_self l hr) (ZMod l)) p
  have k1 := key hq.unit π (by rw [hπ, map_natCast]; rfl)
  have k2 := key (hq.unit ^ 2) (π ^ 2) (by rw [Units.val_pow_eq_pow_val, map_pow, hπ, map_natCast]; rfl)
  rw [hπ', hrq, h1] at k1
  rw [Units.val_pow_eq_pow_val, map_pow, hπ', map_pow, Units.val_pow_eq_pow_val, hrq, one_pow, h1] at k2
  have hpO : (p : Qbar l)⁻¹ ∈ cf.O := hπ' ▸ uO π
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : ‖(p : Qbar l)‖ ≤ 1 := nle cf (natCast_mem _ p)
  refine ⟨fun i => (p : Qbar l)⁻¹ * ∑ y, η y * b y i, fun i => mul_mem hpO (sum_mem fun y _ => mul_mem (ηO y) (hb y i)), fun s i => ?_⟩
  have k3 := key (cycMod ℚ Ω l r s) (cycZ ℚ Ω l s) rfl
  have hth : ((algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]ˣ)) ^ e)⁻¹ * ψ (rd (cycMod ℚ Ω l r s) : (ZMod l)ˣ) = thK l e ψ s := by
    have a1 : rd (cycMod ℚ Ω l r s) = cycM l s := by
      rw [(sCycZ Ω l r s).1]; exact (hS (l ^ r) s).2.2.2.2 l (dvd_pow_self l hr)
    have a2 := (hS (l ^ 1) s).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [← (sCycZ Ω l 1 s).1] at a2
    rw [a1, ← a2, thK, ZMod.natCast_val]; rfl
  rw [hth] at k3
  have h0 := norm_nonneg (((l : ℕ) : Qbar l) ^ r)
  have s1 := shift h0 η (fun y => Y s y i) _ _ k1 fun y => hY s y i
  have s2 := shift h0 η (fun y => Y s y i) _ _ k2 fun y => hY s y i
  have s3 := fun j => shift h0 η (fun y => b y j) _ _ k3 fun y => nle cf (hb y j)
  have s0 := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.univ) h0 fun y _ => smul' (nle cf (ηO y)) (H s y i)
  have hθ0 : thK l e ψ s ≠ 0 := fun h => by simpa [h] using hθ s
  have hWρ : ∀ j, mat W s i j = thK l e ψ s * rhoK W e ψ s i j := fun j => by
    rw [rhoK, Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hθ0]
  have E : ∑ y, η y * (((p : Qbar l) • V s y) i - (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) =
      p * ∑ y, η y * V s y i - (k * (p * ∑ y, η y * Y s y i - a * ∑ y, η y * Y s (y * hq.unit⁻¹) i +
        ((p : Qbar l) ^ (2 * e - 1) * δ) * ∑ y, η y * Y s (y * (hq.unit ^ 2)⁻¹) i) +
        (rhoK W e ψ s i 0 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 0 + rhoK W e ψ s i 1 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 1 -
          ∑ y, η y * b y i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hinv, inv_pow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [E] at s0
  have fin := smul' (nle cf hpO) (sadd (sadd (sadd (sadd s0 (smul' (a := -(k * a)) (by rw [norm_neg]; exact smul' hk ha) s1))
    (smul' (a := k * ((p : Qbar l) ^ (2 * e - 1) * δ)) (smul' hk (smul' (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hpn) hδ)) s2))
    (smul' (nle cf (hρ s i 0)) (s3 0))) (smul' (nle cf (hρ s i 1)) (s3 1)))
  unfold Cg
  convert fin using 2
  simp only [spec, eul, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hWρ]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [show 2 * (e' + 1) - 1 = 2 * e' + 1 by omega]
  field_simp
  ring
