import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHyp

theorem isAdicComplete_of_equiv {Q R : Type*} [CommRing Q] [CommRing R] (e : Q ≃+* R) (a : Q)
    (h : IsAdicComplete (Ideal.span {e a}) R) : IsAdicComplete (Ideal.span {a}) Q := by
  have hmem : ∀ (n : ℕ) (x y : Q),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule Q Q)] ↔
        e x ≡ e y [SMOD (Ideal.span {e a} ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, smul_eq_mul, smul_eq_mul, Ideal.mul_top, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, ← map_pow, ← map_sub]
    exact (map_dvd_iff e).symm
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e x = 0 := by
      refine h.toIsHausdorff.haus' (e x) fun n => ?_
      have := (hmem n x 0).1 (hx n)
      rwa [map_zero] at this
    exact (map_eq_zero_iff e e.injective).1 h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e (f n))
      (fun {m n} hmn => (hmem m _ _).1 (hf hmn))
    refine ⟨e.symm L, fun n => (hmem n _ _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact hL n

variable (l : ℕ) [Fact l.Prime]

def eQ : (Ainf l ⧸ Ideal.span {xi0 l}) ≃+* OC l :=
  (Ideal.quotEquivOfEq (ker_theta0 (l := l)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l))

theorem eQ_natCast (n : ℕ) : eQ l (n : Ainf l ⧸ Ideal.span {xi0 l}) = (n : OC l) := map_natCast _ n

theorem norm_l_lt_one : ‖((l : OC l) : ℂ_[l])‖ < 1 :=
  IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l

theorem l_ne_zero : (l : OC l) ≠ 0 := by
  intro h
  have h1 : ((l : OC l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [h] at h1
  exact (Nat.cast_ne_zero (R := ℂ_[l])).2 (Fact.out : l.Prime).ne_zero (by simpa using h1.symm)

theorem dvd_pow_l {x : OC l} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : OC l) ^ n := by
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxp : 0 < ‖(x : ℂ_[l])‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hxp (norm_l_lt_one l)
  refine ⟨n, ⟨((l : OC l) : ℂ_[l]) ^ n / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hn.le hxp.le
  · simp [mul_div_cancel₀ _ hx0]

theorem dvd_total_OC (x y : OC l) : x ∣ y ∨ y ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inr (dvd_zero y)
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  rcases le_total ‖(y : ℂ_[l])‖ ‖(x : ℂ_[l])‖ with h | h
  · refine Or.inl ⟨⟨(y : ℂ_[l]) / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hx0]
  · have hy : y ≠ 0 := by
      rintro rfl
      exact hx0 (norm_eq_zero.1 (le_antisymm (by simpa using h) (norm_nonneg _)))
    have hy0 : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    refine Or.inr ⟨⟨(x : ℂ_[l]) / y, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hy0]

theorem unit_ainf (n : ℕ) (hn : n ≠ 0) : ∃ (k : ℕ) (u : Ainf l), (n : Ainf l) * u = (l : Ainf l) ^ k := by
  have h0 : (n : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  refine ⟨(n : ℤ_[l]).valuation, IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l
    (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]), ?_⟩
  have h1 : (n : ℤ_[l]) * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ (n : ℤ_[l]).valuation := by
    have e2 := congrArg (· * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) (PadicInt.unitCoeff_spec h0)
    refine e2.trans ?_
    change ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]) * _ * _ = _
    rw [mul_comm ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]), mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) h1
  simpa only [map_mul, map_pow, map_natCast] using h2

abbrev xiB : BdRp l := wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)

theorem span_xiB : Ideal.span {xiB l} = Ideal.span {tBdR l} := by
  rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
  exact maximalIdeal_eq_span_tBdR

theorem xi_dvd_fontaine_t : xiB l ∣ tBdR l :=
  Ideal.mem_span_singleton.1 ((span_xiB l).symm ▸ Ideal.mem_span_singleton_self _)

theorem t_dvd_xiB : tBdR l ∣ xiB l :=
  Ideal.mem_span_singleton.1 ((span_xiB l) ▸ Ideal.mem_span_singleton_self _)

theorem xiB_ne_zero : xiB l ≠ 0 :=
  (IsPerfectoidField.irreducible_wittToBDeRhamPlus (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))).ne_zero

theorem nil_k (k : ℕ) : fk l k (xi0 l) ^ k = 0 := by
  change Ideal.Quotient.mk _ (xiB l) ^ k = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (t_dvd_xiB l) k))

theorem dvd_of_witt_mem {a : Ainf l} (h : xiB l ∣ wittToBDeRhamPlus (normInteger ℂ_[l]) l a) : xi0 l ∣ a := by
  have h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
    exact Ideal.mem_span_singleton.2 h
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l), RingHom.mem_ker,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h1
  have h2 : a ∈ RingHom.ker (theta0 l) := Subtype.ext h1
  rw [ker_theta0] at h2
  exact Ideal.mem_span_singleton.1 h2

theorem gr_k (k i : ℕ) (hi : i < k) (a : Ainf l) (b : Bk l k)
    (h : fk l k a * fk l k (xi0 l) ^ i = fk l k (xi0 l) ^ (i + 1) * b) : xi0 l ∣ a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply dvd_of_witt_mem
  set w := wittToBDeRhamPlus (normInteger ℂ_[l]) l a with hw
  have h1 : Ideal.Quotient.mk (Ideal.span {tBdR l ^ k}) (w * xiB l ^ i) =
      Ideal.Quotient.mk _ (xiB l ^ (i + 1) * b) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  have h3 : xiB l ^ (i + 1) ∣ tBdR l ^ k :=
    (pow_dvd_pow _ hi).trans (pow_dvd_pow_of_dvd (xi_dvd_fontaine_t l) k)
  have h4 : xiB l ^ (i + 1) ∣ w * xiB l ^ i := by
    obtain ⟨c, hc⟩ := h3.trans h2
    exact ⟨c + b, by linear_combination hc⟩
  rw [pow_succ', mul_comm w, mul_comm (xiB l)] at h4
  exact (mul_dvd_mul_iff_left (pow_ne_zero i (xiB_ne_zero l))).1 h4

theorem hyp_k (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) : Lat.Hyp (Lat.fk l k) (xi0 l) l k := by
  have hl : eQ l (l : Ainf l ⧸ Ideal.span {xi0 l}) = (l : OC l) := eQ_natCast l l
  refine
    { one_le := hk
      nil := nil_k l k
      gr := fun i hi a b h => gr_k l k i hi a b h
      dom := (eQ l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := fun h => ?_
      cpl := ?_
      unit := unit_ainf l }
  · rcases dvd_total_OC l (eQ l x) (eQ l y) with h | h
    · exact Or.inl ((map_dvd_iff (eQ l)).1 h)
    · exact Or.inr ((map_dvd_iff (eQ l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_l l (x := eQ l x) ((map_ne_zero_iff _ (eQ l).injective).2 hx)
    refine ⟨n, (map_dvd_iff (eQ l)).1 ?_⟩
    rwa [map_pow, hl]
  · apply l_ne_zero l
    rw [← hl, h, map_zero]
  · refine isAdicComplete_of_equiv (eQ l) _ ?_
    rw [hl]
    exact IsPerfectoidField.isAdicComplete (K := ℂ_[l]) l

end GlobalTheory.CompanionTheory.LatCHyp
