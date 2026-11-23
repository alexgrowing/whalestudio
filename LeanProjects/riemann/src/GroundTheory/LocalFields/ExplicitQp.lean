import Mathlib
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.LocalFields.LocalReciprocityUniversal

noncomputable section

open IntermediateField ValuativeRel

namespace GroundTheory.LocalField

open Abstract GroundTheory.LocalField.FormalGroup

section Bridge

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hf in

theorem localReciprocity_symm_lubinTateField {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    {τ : Ω ≃ₐ[K] Ω} (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (localReciprocity (lubinTateField Ω hπ hf n)).symm
        (unitUniformizerPow hπ u k : Kˣ ⧸ (normUnits K (lubinTateField Ω hπ hf n)).range) =
      Abelianization.of (τ.restrictNormal (lubinTateField Ω hπ hf n)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set L := lubinTateField Ω hπ hf n
  have hr := reciprocity_lubinTate hπ hf hn (fixingOpenSubgroup L)
    (by rw [coe_fixingOpenSubgroup]) (by rw [coe_fixingOpenSubgroup]; exact inf_le_left) u k τ hτd hτ
  obtain ⟨a, ha⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective (unitUniformizerPow hπ u k)
  rw [← ha, MulEquiv.symm_apply_apply] at hr
  rw [← ha, localReciprocity_symm_mk_baseUnitsEquiv]
  have e : ((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _) =
      Abelianization.of (QuotientGroup.mk ⟨τ, Subgroup.mem_top τ⟩) := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of]
    exact hr.symm
  rw [e]
  rfl

include hf in

theorem apply_val_of_mk_eq_localReciprocityLimit {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
      localReciprocityLimit K Ω (unitUniformizerPow hπ u k))
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    g x.val = (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set L := lubinTateField Ω hπ hf n
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨lubinTateField_mul_comm hπ hf n⟩⟩
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u k
  have h2 := of_abelianRestrict_localReciprocityLimit L (unitUniformizerPow hπ u k)
  rw [← hg, abelianRestrict_mk, localReciprocity_symm_lubinTateField hπ hf hn u k hτd hτ] at h2
  have h3 := (bijective_abelianizationOf L).1 h2
  have hxL := val_mem_lubinTateField hπ hf hx
  have e := congrArg IdealPoint.val (hτ x hx)
  rw [lubinTateGalPointMap_val] at e
  rw [← e]
  have c1 := AlgEquiv.restrictNormal_commutes g L ⟨x.val, hxL⟩
  have c2 := AlgEquiv.restrictNormal_commutes τ L ⟨x.val, hxL⟩
  rw [h3] at c1
  exact c1.symm.trans c2

end Bridge

section Multiplicative

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem subst_multiplicativeLTPoly {τ : Type*} {a : MvPowerSeries τ 𝒪[ℚ_[p]]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) = (1 + a) ^ p - 1 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [multiplicativeLTPoly, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_X, ← PowerSeries.coe_substAlgHom hs, map_sub, map_pow,
    map_add, map_one, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs]

theorem lubinTateFormalGroup_multiplicative :
    (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p)).toPowerSeries =
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) := by
  rw [lubinTateFormalGroup_toPowerSeries]
  symm
  apply eq_lubinTateLift
  · rw [linearForm_fin_two, map_one, one_mul, one_mul, add_sub_cancel_left]
    have h1 : ∀ i : Fin 2, (1 : ℕ∞) ≤ MvPowerSeries.order (MvPowerSeries.X i :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) :=
      fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 (by simp)
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add (h1 0) (h1 1)
      _ ≤ _ := MvPowerSeries.le_order_mul
  · have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) = 0 := by simp
    have hs : MvPowerSeries.HasSubst (substEach (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) :
        Fin 2 → MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) :=
      hasSubst_substEach (isLubinTateSeries_multiplicativeLTPoly p).constantCoeff_eq_zero
    rw [subst_multiplicativeLTPoly p h0, ← MvPowerSeries.coe_substAlgHom hs, map_add, map_add,
      map_mul, MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_X hs,
      MvPowerSeries.subst_X hs, substEach_apply, substEach_apply,
      subst_multiplicativeLTPoly p (by simp), subst_multiplicativeLTPoly p (by simp)]
    rw [show (1 + (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) = (1 + MvPowerSeries.X 0) * (1 + MvPowerSeries.X 1) by ring,
      mul_pow]
    ring

end Padic

end Multiplicative

section Points

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem psTerm_add {σ : Type*} (f g : MvPowerSeries σ 𝒪[K]) (x : σ → Ω) :
    psTerm (f + g) x = psTerm f x + psTerm g x := by
  funext d
  simp only [psTerm, map_add, Subring.coe_add, Pi.add_apply, add_mul]

theorem psEval_add {σ : Type*} [Finite σ] (f g : MvPowerSeries σ 𝒪[K]) {x : σ → Ω}
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (f + g) x = psEval f x + psEval g x := by
  have := t2Space_of_isValuativeTopology Ω
  have h := (hasSum_psEval' f x hx).add (hasSum_psEval' g x hx)
  exact (hasSum_psEval' (f + g) x hx).unique (by rw [psTerm_add]; exact h)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem psEval_X_mul_X [TopologicalSpace Ω] (x : Fin 2 → Ω) :
    psEval (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[K]) x = x 0 * x 1 := by
  classical
  have hX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[K]) =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [hX, psEval, tsum_eq_single (Finsupp.single 0 1 + Finsupp.single 1 1)]
  · rw [psTerm, MvPowerSeries.coeff_monomial_same, Finsupp.prod_add_index (by simp) (by simp [pow_add])]
    simp
  · intro d hd
    simp [psTerm, MvPowerSeries.coeff_monomial, hd]

end Points

section PadicPoints

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra ℚ_[p] Ω] [ValuativeExtension ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem val_add_multiplicative
    (x y : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (x + y).val = x.val + y.val + x.val * y.val := by
  have hxy : ∀ i, valuation Ω ((![x.val, y.val] : Fin 2 → Ω) i) < 1 := fun i => by
    fin_cases i
    · exact x.valuation_lt_one
    · exact y.valuation_lt_one
  rw [IdealPoint.val_add, lubinTateFormalGroup_multiplicative, psEval_add _ _ hxy,
    psEval_add _ _ hxy, psEval_X, psEval_X, psEval_X_mul_X]
  rfl

theorem val_natCast_smul (k : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (((k : 𝒪[ℚ_[p]])) • x).val = (1 + x.val) ^ k - 1 := by
  rw [Nat.cast_smul_eq_nsmul]
  induction k with
  | zero => simp [IdealPoint.val_zero]
  | succ k ih =>
    rw [succ_nsmul, val_add_multiplicative, ih, pow_succ]
    ring

theorem val_smul_of_mem_torsion {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))}
    (hx : x ∈ lubinTateTorsion Ω (isLubinTateSeries_multiplicativeLTPoly p) n) {a : 𝒪[ℚ_[p]]} {k : ℕ}
    (hak : (p : 𝒪[ℚ_[p]]) ^ n ∣ a - k) :
    (a • x).val = (1 + x.val) ^ k - 1 := by
  obtain ⟨c, hc⟩ := hak
  have h0 : ((p : 𝒪[ℚ_[p]]) ^ n) • x = 0 := (mem_lubinTateTorsion _ n x).1 hx
  have : a • x = (k : 𝒪[ℚ_[p]]) • x := by
    rw [← sub_eq_zero, ← sub_smul, hc, mul_comm, mul_smul, h0, smul_zero]
  rw [this, val_natCast_smul]

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic ℚ_[p] Ω] in

theorem valuation_sub_one_lt_one {n : ℕ} {ζ : Ω} (hζ : ζ ^ (p ^ n) = 1) :
    valuation Ω (ζ - 1) < 1 := by
  have hp1 : valuation Ω (p : Ω) < 1 := by
    have h := valuation_algebraMap_lt_one_of_irreducible (L := Ω) (irreducible_natCast_integer p)
    simpa using h
  induction n generalizing ζ with
  | zero =>
    rw [pow_zero, pow_one] at hζ
    simp [hζ]
  | succ n ih =>
    have h1 : (ζ ^ p) ^ (p ^ n) = 1 := by rw [← pow_mul, ← pow_succ']; exact hζ
    have ih' := ih h1
    by_contra hge
    replace hge := not_lt.1 hge
    have hv1 : valuation Ω ζ = 1 := by
      have hN : valuation Ω ζ ^ (p ^ (n + 1)) = 1 := by rw [← map_pow, hζ, map_one]
      have hN0 : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
      rcases lt_trichotomy (valuation Ω ζ) 1 with h | h | h
      · exact absurd hN (pow_lt_one₀ zero_le h hN0).ne
      · exact h
      · exact absurd hN (one_lt_pow₀ h hN0).ne'
    have hle : valuation Ω (ζ - 1) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (by simp [hv1])
    have heq : valuation Ω (ζ - 1) = 1 := le_antisymm hle hge
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out
      (⟨ζ - 1, (Valuation.mem_integer_iff _ _).2 hle⟩ : 𝒪[Ω]) 1
    have e : ζ ^ p - 1 = (ζ - 1) ^ p + (p : Ω) * (ζ - 1) * (r : Ω) := by
      have := congrArg Subtype.val hr
      simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_one,
        Subring.coe_natCast, one_pow, mul_one, sub_add_cancel] at this
      rw [this]
      ring
    have hr1 : valuation Ω (r : Ω) ≤ 1 := (Valuation.mem_integer_iff _ _).1 r.2
    have hlt : valuation Ω ((p : Ω) * (ζ - 1) * (r : Ω)) < valuation Ω ((ζ - 1) ^ p) := by
      rw [map_pow, heq, one_pow, map_mul, map_mul, heq, mul_one]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hr1) hp1
    have : valuation Ω (ζ ^ p - 1) = 1 := by
      rw [e, (valuation Ω).map_add_eq_of_lt_left hlt, map_pow, heq, one_pow]
    exact absurd ih' (by rw [this]; exact lt_irrefl 1)

end Padic

end PadicPoints

section Explicit

theorem pow_eq_pow_of_natCast_eq {M : Type*} [Monoid M] {ξ : M} {m a b : ℕ} (hξ : ξ ^ m = 1)
    (h : (a : ZMod m) = b) : ξ ^ a = ξ ^ b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  have key : ∀ c, ξ ^ c = ξ ^ (c % m) := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c m, pow_add, pow_mul, hξ, one_pow, one_mul]
  rw [key a, key b, h]

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

theorem natCast_residueField_ne_zero {m : ℕ} (hm : m.Coprime p) : (m : 𝓀[ℚ_[p]]) ≠ 0 := by
  intro h0
  have hcard : ((Nat.card 𝓀[ℚ_[p]] : ℕ) : 𝓀[ℚ_[p]]) = 0 := by
    have := Fintype.ofFinite 𝓀[ℚ_[p]]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[ℚ_[p]]
  rw [card_residueField] at hcard
  have hc : ringChar 𝓀[ℚ_[p]] ∣ p :=
    (CharP.cast_eq_zero_iff 𝓀[ℚ_[p]] (ringChar 𝓀[ℚ_[p]]) p).1 hcard
  have hcp : ringChar 𝓀[ℚ_[p]] = p :=
    ((Nat.dvd_prime hp.out).1 hc).resolve_left CharP.ringChar_ne_one
  have hdvd : p ∣ m := by
    rw [← hcp, ← CharP.cast_eq_zero_iff 𝓀[ℚ_[p]] (ringChar 𝓀[ℚ_[p]])]
    exact h0
  have h := Nat.Coprime.coprime_dvd_left hdvd hm
  rw [Nat.coprime_self] at h
  exact hp.out.one_lt.ne' h

theorem frobenius_zpow_apply_of_pow_eq_one {m : ℕ} (hm : m.Coprime p) (r : ℤ)
    {ξ : maximalUnramifiedExtension ℚ_[p] Ω} (hξ : ξ ^ m = 1) :
    (maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ r) ξ =
      ξ ^ (((ZMod.unitOfCoprime p hm.symm ^ r : (ZMod m)ˣ) : ZMod m)).val := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have : NeZero m := ⟨hm0⟩
  set F := maximalUnramifiedExtensionFrobenius ℚ_[p] Ω
  set e := ZMod.unitOfCoprime p hm.symm
  have he : ((e : (ZMod m)ˣ) : ZMod m) = p := ZMod.coe_unitOfCoprime p hm.symm
  have hF : ∀ η : maximalUnramifiedExtension ℚ_[p] Ω, η ^ m = 1 → F η = η ^ p := fun η hη => by
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
      (natCast_residueField_ne_zero p hm) hη, card_residueField]
  have hnat : ∀ (k : ℕ) (η : maximalUnramifiedExtension ℚ_[p] Ω), η ^ m = 1 →
      (F ^ k) η = η ^ (((e ^ k : (ZMod m)ˣ) : ZMod m)).val := by
    intro k
    induction k with
    | zero =>
      intro η hη
      rw [pow_zero, pow_zero, Units.val_one, AlgEquiv.one_apply]
      conv_lhs => rw [← pow_one η]
      exact pow_eq_pow_of_natCast_eq hη (by rw [ZMod.natCast_zmod_val, Nat.cast_one])
    | succ k ih =>
      intro η hη
      have hk : ((F ^ k) η) ^ m = 1 := by rw [← map_pow, hη, map_one]
      rw [pow_succ', AlgEquiv.mul_apply, hF _ hk, ih η hη, ← pow_mul]
      refine pow_eq_pow_of_natCast_eq hη ?_
      rw [ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val, pow_succ, Units.val_mul, he]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg r
  · rw [zpow_natCast, zpow_natCast]
    exact hnat k ξ hξ
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    set η := (F ^ k)⁻¹ ξ
    have hη : η ^ m = 1 := by rw [← map_pow, hξ, map_one]
    have hFη : (F ^ k) η = ξ := by
      change (F ^ k) ((F ^ k).symm ξ) = ξ
      exact AlgEquiv.apply_symm_apply _ ξ
    rw [← hFη, hnat k η hη, ← pow_mul]
    conv_lhs => rw [← pow_one η]
    refine pow_eq_pow_of_natCast_eq hη ?_
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Nat.cast_one]

def integerUnit (u : ℤ_[p]ˣ) : 𝒪[ℚ_[p]]ˣ :=
  Units.map (PadicRank.padicIntEquivInteger p : ℤ_[p] →* 𝒪[ℚ_[p]]) u

theorem coe_integerUnit (u : ℤ_[p]ˣ) :
    (((integerUnit p u : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) :=
  rfl

theorem unitUniformizerPow_integerUnit (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) :
    unitUniformizerPow (irreducible_natCast_integer p) (integerUnit p u) r = x := by
  apply Units.ext
  rw [hx, unitUniformizerPow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val,
    Units.val_mk0]
  rfl

theorem ord_eq_of_eq_mul_zpow (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) :
    ord (x : ℚ_[p]) = r := by
  have hπ := irreducible_natCast_integer p
  have hp0 : (((p : 𝒪[ℚ_[p]]) : ℚ_[p])) ≠ 0 := coe_ne_zero_of_irreducible hπ
  have e : (x : ℚ_[p]) = (((integerUnit p u : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) : ℚ_[p]) *
      ((p : 𝒪[ℚ_[p]]) : ℚ_[p]) ^ r := by
    rw [← unitUniformizerPow_integerUnit p x u r hx, unitUniformizerPow, Units.val_mul,
      Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  rw [e, ord_mul (by simp) (zpow_ne_zero _ hp0), ord_unit, ord_zpow hp0, ord_uniformizer hπ,
    mul_one, zero_add]

theorem apply_of_pow_eq_one_of_prime_pow (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {n : ℕ} {ζ : Ω} (hζ : ζ ^ (p ^ n) = 1) :
    σ ζ = ζ ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hζ
    subst hζ
    simp
  have hπ := irreducible_natCast_integer p
  have hf := isLubinTateSeries_multiplicativeLTPoly p
  set k := (PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val
  let y : IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
    IdealPoint.mk (ζ - 1) (valuation_sub_one_lt_one p hζ)
  have hy : y ∈ lubinTateTorsion Ω hf n := by
    rw [mem_lubinTateTorsion]
    apply IdealPoint.ext
    rw [val_pow_smul, IdealPoint.val_zero, IdealPoint.val_mk, add_sub_cancel, hζ, sub_self]
  have h1 := apply_val_of_mk_eq_localReciprocityLimit hπ hf hn (integerUnit p u) r
    (hσ.trans (by rw [unitUniformizerPow_integerUnit p x u r hx])) hy
  have hdvd : (p : 𝒪[ℚ_[p]]) ^ n ∣ (((integerUnit p u)⁻¹ : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) - k := by
    have hker : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - k ∈ RingHom.ker (PadicInt.toZModPow (p := p) n) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    have h := map_dvd (PadicRank.padicIntEquivInteger p) hker
    rw [map_pow, map_natCast, map_sub, map_natCast] at h
    convert h using 2
    simp [integerUnit]
  rw [val_smul_of_mem_torsion p hy hdvd] at h1
  simp only [y, IdealPoint.val_mk, add_sub_cancel, map_sub, map_one] at h1
  exact sub_left_injective h1

theorem apply_of_pow_eq_one_of_coprime (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {m : ℕ} (hm : m.Coprime p) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ (((ZMod.unitOfCoprime p hm.symm ^ r : (ZMod m)ˣ) : ZMod m)).val := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed ℚ_[p]
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    subst h
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have hζur : ζ ∈ maximalUnramifiedExtension ℚ_[p] Ω := by
    rw [maximalUnramifiedExtension_eq_adjoin_rootsOfUnity]
    exact subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩
  have hdeg := unramifiedDegree_of_mk_eq_localReciprocityLimit hσ
  rw [ord_eq_of_eq_mul_zpow p x u r hx] at hdeg
  have hres : σ.restrictNormal (maximalUnramifiedExtension ℚ_[p] Ω) =
      maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ r := by
    apply unramifiedDegree_maximalUnramifiedExtension_injective
    rw [unramifiedDegree_restrictNormal, hdeg, map_zpow,
      unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]
  have hξ : (⟨ζ, hζur⟩ : maximalUnramifiedExtension ℚ_[p] Ω) ^ m = 1 :=
    Subtype.ext (by simpa using hζ)
  have c := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension ℚ_[p] Ω) ⟨ζ, hζur⟩
  rw [hres] at c
  rw [frobenius_zpow_apply_of_pow_eq_one p hm r hξ] at c
  change ((⟨ζ, hζur⟩ ^ _ : maximalUnramifiedExtension ℚ_[p] Ω) : Ω) = σ ζ at c
  rw [← c, SubmonoidClass.coe_pow]

theorem apply_of_pow_eq_one_of_coprime_of_nat (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℕ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {m : ℕ} (hm : m.Coprime p) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ (p ^ r) := by
  have hm0 : m ≠ 0 := fun h => by
    subst h
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have : NeZero m := ⟨hm0⟩
  rw [apply_of_pow_eq_one_of_coprime p x u r (by rw [hx, zpow_natCast]) hσ hm hζ]
  refine pow_eq_pow_of_natCast_eq hζ ?_
  rw [ZMod.natCast_zmod_val, zpow_natCast, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    Nat.cast_pow]

end Padic

end Explicit

end GroundTheory.LocalField
