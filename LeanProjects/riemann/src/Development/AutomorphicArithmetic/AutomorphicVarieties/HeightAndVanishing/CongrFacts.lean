import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

section Loc

variable {O : Type} [CommRing O] [IsLocalRing O]

private theorem sub_mem_iff (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ IsLocalRing.residue O x = IsLocalRing.residue O y := by
  exact (Ideal.Quotient.eq).symm

private theorem res_eq_one (l : ℕ) [hl : Fact l.Prime] (h : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hx : x ^ l ^ s = 1) :
    IsLocalRing.residue O x = 1 := by
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact h
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 : (IsLocalRing.residue O x - 1) ^ l ^ s = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hx, map_one, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero s hl.out.ne_zero) |>.1 h1)

private theorem eq_of_res_eq [IsDomain O] (x y : Oˣ) (m : ℕ) (hm : IsUnit (m : O)) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  have hw : (x * y⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hr : IsLocalRing.residue O ((x * y⁻¹ : Oˣ) : O) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hzm : ((x * y⁻¹ : Oˣ) : O) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hs : IsUnit (∑ i ∈ Finset.range m, ((x * y⁻¹ : Oˣ) : O) ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (IsLocalRing.residue O) m]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hm
  have e := geom_sum_mul ((x * y⁻¹ : Oˣ) : O) m
  rw [hzm, sub_self] at e
  have hz1 := (hs.mul_right_eq_zero).mp e
  have h1 : x * y⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp hz1)
  exact mul_inv_eq_one.mp h1

private theorem res_inv (x : Oˣ) : IsLocalRing.residue O ((x⁻¹ : Oˣ) : O) = (IsLocalRing.residue O x)⁻¹ := by
  exact map_units_inv (IsLocalRing.residue O) x

end Loc

theorem UpperTheory.V.HV.congrFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), Equivalence (Congr (Ω := Ω) c) ∧
      (∀ a a' b b' : G ℚ Ω →* c.Oˣ, Congr c a a' → Congr c b b' → Congr c (a * b) (a' * b') ∧ Congr c a⁻¹ a'⁻¹) ∧
      (∀ (a : G ℚ Ω →* c.Oˣ) (s : ℕ), a ^ l ^ s = 1 → Congr c a 1) ∧
      (∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 → (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y) ∧
      ∀ (a b : G ℚ Ω →* c.Oˣ) (m : ℕ), ¬ l ∣ m → a ^ m = 1 → b ^ m = 1 → Congr c a b → a = b := by
  intro Ω _ _ _ l _ c
  haveI := c.dvr
  haveI := c.fin
  have hF := dvrFacts l c.O
  have hlu : ¬ IsUnit ((l : ℕ) : c.O) := by
    intro hu
    have hu' : IsUnit (algebraMap ℤ_[l] c.O ((l : ℕ) : ℤ_[l])) := by rwa [map_natCast]
    haveI := hF.2.2.1
    exact PadicInt.p_nonunit (IsLocalHom.map_nonunit _ hu')
  have cr : ∀ a b : G ℚ Ω →* c.Oˣ, Congr c a b ↔
      ∀ σ, IsLocalRing.residue c.O (a σ : c.O) = IsLocalRing.residue c.O (b σ : c.O) :=
    fun a b => forall_congr' fun σ => sub_mem_iff _ _
  have p4 : ∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 →
      (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y :=
    fun x y m hm hx hy hxy => eq_of_res_eq x y m (hF.2.2.2.2.2.2.2.2 m hm) hx hy ((sub_mem_iff _ _).mp hxy)
  have papp : ∀ (a : G ℚ Ω →* c.Oˣ) (n : ℕ), a ^ n = 1 → ∀ σ, (a σ) ^ n = 1 := by
    intro a n ha σ
    rw [← MonoidHom.pow_apply, ha, MonoidHom.one_apply]
  refine ⟨⟨fun a => ?_, fun {a b} h => ?_, fun {a b d} h1 h2 => ?_⟩, fun a a' b b' ha hb => ⟨?_, ?_⟩,
    fun a s ha => ?_, p4, fun a b m hm ha hb hab => ?_⟩
  · rw [cr]
    intro σ
    rfl
  · rw [cr] at h ⊢
    intro σ
    exact (h σ).symm
  · rw [cr] at h1 h2 ⊢
    intro σ
    exact (h1 σ).trans (h2 σ)
  · rw [cr] at ha hb ⊢
    intro σ
    simp only [MonoidHom.mul_apply, Units.val_mul, map_mul, ha σ, hb σ]
  · rw [cr] at ha ⊢
    intro σ
    simp only [MonoidHom.inv_apply, res_inv, ha σ]
  · rw [cr]
    intro σ
    have e' : ((a σ : c.O)) ^ l ^ s = 1 := by
      rw [← Units.val_pow_eq_pow_val, papp a _ ha σ, Units.val_one]
    rw [res_eq_one l hlu _ s e', MonoidHom.one_apply, Units.val_one, map_one]
  · apply MonoidHom.ext
    intro σ
    exact p4 _ _ m hm (papp a m ha σ) (papp b m hb σ) (hab σ)
