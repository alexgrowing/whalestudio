import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem res_zpow {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (n : ℤ) :
    residue O ((u ^ n : Oˣ) : O) = residue O (u : O) ^ n := by
  rcases n with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  · rw [zpow_negSucc, zpow_negSucc]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_mul, Units.inv_mul, map_one]

private theorem res_ne {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) : residue O (u : O) ≠ 0 :=
  (u.isUnit.map (residue O)).ne_zero

private theorem bar_mul_frobenius_fields {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f h : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) : Raw.bar (f * h) g = Raw.bar f g * Raw.bar h g := by
  unfold Raw.bar
  rw [MonoidHom.mul_apply, Units.val_mul, map_mul]

private theorem bar_inv' {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) : Raw.bar f⁻¹ g = (Raw.bar f g)⁻¹ := by
  unfold Raw.bar
  rw [MonoidHom.inv_apply, ← zpow_neg_one, res_zpow, zpow_neg_one]

private theorem bar_pow' {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (f : G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar (f ^ n) g = Raw.bar f g ^ n := by
  unfold Raw.bar
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow]

theorem UpperTheory.V.Ws.barFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (-1 : ResidueField c.O) ≠ 1 ∧ (∀ (x : ResidueField c.O) (j : ℕ), x ^ l ^ j = 1 → x = 1) ∧ (∀ g, Raw.bar D.al g = Raw.bar D.ξ g) ∧ (∀ g, Raw.bar D.th g = Raw.bar D.ξ g * Raw.bar D.Psi g) ∧ (∀ g, Raw.bar D.Psi g = Raw.bar D.om g ^ D.e * Raw.bar D.ψ g) ∧ (∀ g, D.rbar g = 1 ↔ Raw.bar D.ξ g = 1 ∧ Raw.bar D.Psi g = 1) ∧ (∀ (T : Tower D) (w : ℤ × ℤ) (g : G T.F Ω), T.rb w g = Raw.bar D.ξ (resQ T.F g) ^ w.1 * Raw.bar D.Psi (resQ T.F g) ^ (if T.pr then -w.2 else w.2)) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g, Raw.bar D.Psi g ^ m = 1) ∧ IsOpen {g | Raw.bar D.Psi g = 1} := by
  intro Ω _ _ _ l _ c D hD
  have hmax : ∀ x ∈ maximalIdeal c.O, residue c.O x = 0 := fun x hx => (residue_eq_zero_iff x).mpr hx
  obtain ⟨hchar, hfin⟩ := Gys.coefFacts c (ResidueField c.O) (residue c.O) hmax
  have hl2 : l ≠ 2 := hD.l_odd
  have hlp : l.Prime := Fact.out
  have hal : ∀ g, Raw.bar D.al g = Raw.bar D.ξ g := by
    intro g
    have e1 : D.al = chiO ℚ Ω l c.O * D.om⁻¹ * D.ξ := by
      unfold Raw.al
      rfl
    rw [e1, bar_mul_frobenius_fields, bar_mul_frobenius_fields, bar_inv', ← hD.om_bar g, mul_inv_cancel₀ (res_ne _), one_mul]
  have hth : ∀ g, Raw.bar D.th g = Raw.bar D.ξ g * Raw.bar D.Psi g := by
    intro g
    have e1 : D.th = D.al * D.Psi := by
      unfold Raw.th
      rfl
    rw [e1, bar_mul_frobenius_fields, hal]
  have hPsi : ∀ g, Raw.bar D.Psi g = Raw.bar D.om g ^ D.e * Raw.bar D.ψ g := by
    intro g
    have e1 : D.Psi = chiO ℚ Ω l c.O ^ D.e * D.ψ := by
      unfold Raw.Psi UpperTheory.V.Chr.Psi
      rfl
    rw [e1, bar_mul_frobenius_fields, bar_pow', hD.om_bar g]
  haveI : Finite (ResidueField c.O) := by
    rw [Set.range_eq_univ.mpr residue_surjective] at hfin
    exact Set.finite_univ_iff.mp hfin
  haveI := Fintype.ofFinite (ResidueField c.O)
  have hneg : (-1 : ResidueField c.O) ≠ 1 := by
    apply Ring.neg_one_ne_one_of_char_ne_two
    rw [ringChar.eq (ResidueField c.O) l]
    exact hl2
  have hfrob : ∀ (x : ResidueField c.O) (j : ℕ), x ^ l ^ j = 1 → x = 1 := by
    intro x j hx
    have h0 : (x - 1) ^ l ^ j = 0 := by
      rw [sub_pow_char_pow, hx, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero j hlp.ne_zero)).mp h0)
  have hr : ∀ g, D.rbar g = 1 ↔ Raw.bar D.ξ g = 1 ∧ Raw.bar D.Psi g = 1 := by
    intro g
    unfold Raw.rbar mapRep Raw.r0 diagRep
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    show (Matrix.diagonal fun i => ((D.ps i g : (c.O)ˣ) : c.O)).map (residue c.O) = 1 ↔ _
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    have h1 := hal g
    have h2 := hth g
    unfold Raw.bar at h1 h2 ⊢
    simp [Fin.forall_fin_succ, Raw.ps, h1, h2]
    constructor
    · rintro ⟨-, hp, hx⟩
      exact ⟨hx, hp⟩
    · rintro ⟨hx, hp⟩
      exact ⟨by rw [hx, hp, one_mul], hp, hx⟩
  have hrb : ∀ (T : Tower D) (w : ℤ × ℤ) (g : G T.F Ω), T.rb w g = Raw.bar D.ξ (resQ T.F g) ^ w.1 * Raw.bar D.Psi (resQ T.F g) ^ (if T.pr then -w.2 else w.2) := by
    intro T w g
    unfold Tower.rb
    simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply]
    unfold chi
    generalize resQ T.F g = τ
    have e1 : D.th τ = D.al τ * D.Psi τ := by
      unfold Raw.th
      rfl
    have hinv : ∀ u : (c.O)ˣ, residue c.O ((u⁻¹ : (c.O)ˣ) : c.O) = (residue c.O (u : c.O))⁻¹ := fun u => by
      rw [← zpow_neg_one, res_zpow, zpow_neg_one]
    have hal' : residue c.O (D.al τ : c.O) = residue c.O (D.ξ τ : c.O) := hal τ
    have ha := res_ne (D.al τ)
    have hp := res_ne (D.Psi τ)
    unfold Raw.bar
    rw [← hal']
    cases T.pr <;> simp [lab, Raw.ps, e1, hinv, res_zpow, ha, hp, inv_zpow]
  have hm : ∃ m : ℕ, l.Coprime m ∧ ∀ g, Raw.bar D.Psi g ^ m = 1 := by
    refine ⟨Fintype.card (ResidueField c.O) - 1, ?_, fun g => ?_⟩
    · obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField c.O) l
      rw [hn]
      have h1 : Nat.Coprime (l ^ (n : ℕ)) (l ^ (n : ℕ) - 1) :=
        (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hlp.pos)).mpr (Nat.coprime_one_right _)
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self l n.ne_zero) h1
    · unfold Raw.bar
      exact FiniteField.pow_card_sub_one_eq_one _ (res_ne _)
  have hopen : IsOpen {g | Raw.bar D.Psi g = 1} := by
    have homT : IsOmT c D.om := by
      unfold IsOmT
      refine ⟨hD.om_pow, fun σ => ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact hD.om_bar σ
    have hom := ((omT Ω l c).2 D.om homT).2.2.2.1
    let H : Subgroup (G ℚ Ω) := ((Units.map (residue c.O : c.O →* ResidueField c.O)).comp D.Psi).ker
    have hset : {g | Raw.bar D.Psi g = 1} = (H : Set (G ℚ Ω)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, H, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one]
      rfl
    rw [hset]
    refine Subgroup.isOpen_mono (H₁ := D.om.ker ⊓ D.ψ.ker) ?_ (hom.inter hD.psi_open)
    intro g hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    rw [MonoidHom.mem_ker] at h1 h2
    have : Raw.bar D.Psi g = 1 := by
      rw [hPsi]
      unfold Raw.bar
      rw [h1, h2, Units.val_one, map_one, one_pow, one_mul]
    rw [← SetLike.mem_coe, ← hset]
    exact this
  exact ⟨hneg, hfrob, hal, hth, hPsi, hr, hrb, hm, hopen⟩
