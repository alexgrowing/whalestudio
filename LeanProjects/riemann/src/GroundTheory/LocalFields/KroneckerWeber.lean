import Mathlib
import GroundTheory.LocalFields.Existence
import GroundTheory.LocalFields.LubinTateLimit
import GroundTheory.LocalFields.PrincipalUnitsRank
import GroundTheory.LocalFields.MaximalAbelianExtension

noncomputable section

open IntermediateField ValuativeRel

namespace GroundTheory.LocalField

open Abstract GroundTheory.LocalField.FormalGroup

section Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem mul_comm_of_isAbelianGalois (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  (IsMulCommutative.is_comm (M := L ≃ₐ[K] L)).comm σ τ

theorem isAbelianGalois_of_mul_comm (L : IntermediateField K Ω) [IsGalois K L]
    (h : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) : IsAbelianGalois K L where
  is_comm := ⟨h⟩

end Abelian

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosed Ω] [Algebra.IsSeparable K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hf in

theorem isAbelianGalois_lubinTateField_sup {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) :
    IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) := by
  have := hE.1
  have := hE.isGalois
  exact isAbelianGalois_of_mul_comm _ (lubinTateUnramified_mul_comm hπ hf hn hE)

include hf in

theorem exists_le_lubinTateField_sup_unramifiedTower (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ n m : ℕ, L ≤ lubinTateField Ω hπ hf (n + 1) ⊔ unramifiedTower K Ω m := by
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨hO, hF⟩ := isOpen_range_normUnits_and_finiteIndex L
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hO
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  have hle := range_normUnits_sup_le hπ hf n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH
  have hM := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  exact ⟨n, m, (range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois _)
    (mul_comm_of_isAbelianGalois L)).1 hle⟩

theorem maximalAbelianExtension_eq_lubinTateMaxUnramified :
    maximalAbelianExtension K Ω = lubinTateMaxUnramified Ω hπ := by
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  have hf := isLubinTateSeries_ltPoly π
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
    obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
    exact sup_le_sup (lubinTateField_le_lubinTateLimit hπ hf _)
      (unramifiedTower_le_maximalUnramifiedExtension m) (h hyL)
  · refine @le_maximalAbelianExtension K Ω _ _ _ _ _ (isAbelianGalois_of_mul_comm _ fun σ τ =>
      (lubinTateMaxUnramifiedGalEquiv hπ hf).injective (by rw [map_mul, map_mul, mul_comm]))

end LubinTate

section Padic

namespace Padic

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem irreducible_natCast_integer : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff (f := (PadicRank.padicIntEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

theorem card_residueField : Nat.card 𝓀[ℚ_[p]] = p := by
  rw [← Nat.card_congr (IsLocalRing.ResidueField.mapEquiv
      (PadicRank.padicIntEquivInteger p)).toEquiv,
    Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]

def multiplicativeLTPoly : 𝒪[ℚ_[p]][X] := (1 + X) ^ p - 1

theorem isLubinTateSeries_multiplicativeLTPoly :
    IsLubinTateSeries (p : 𝒪[ℚ_[p]]) (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) where
  constantCoeff_eq_zero := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp
  coeff_one := by
    rw [Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp [Polynomial.coeff_one]
  dvd_coeff_sub n := by
    rw [card_residueField, ← Polynomial.coe_X, ← Polynomial.coe_pow, ← Polynomial.coe_sub,
      Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_sub, coeff_one_add_X_pow,
      coeff_one, coeff_X_pow]
    have hp0 := hp.out.ne_zero
    by_cases h0 : n = 0
    · subst h0
      simp [Ne.symm hp0]
    by_cases hpn : n = p
    · subst hpn
      simp [h0]
    rw [if_neg h0, if_neg hpn, sub_zero, sub_zero]
    rcases lt_or_gt_of_ne hpn with h | h
    · exact Nat.cast_dvd_cast (hp.out.dvd_choose_self h0 h)
    · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
      exact dvd_zero _

section Torsion

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra ℚ_[p] Ω] [ValuativeExtension ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem val_pow_smul (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (((p : 𝒪[ℚ_[p]]) ^ n) • x).val = (1 + x.val) ^ (p ^ n) - 1 := by
  have := t2Space_of_isValuativeTopology Ω
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, ih, lubinTate_uniformizer_smul_val, psEval_polynomial]
    simp only [multiplicativeLTPoly, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X, map_sub, map_pow, map_add, map_one, aeval_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem lubinTateField_le_adjoin_rootsOfUnity (n : ℕ) :
    lubinTateField Ω (irreducible_natCast_integer p) (isLubinTateSeries_multiplicativeLTPoly p) n ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ n) = 1} := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have h := congrArg IdealPoint.val ((mem_lubinTateTorsion _ n x).1 hx)
  rw [val_pow_smul, IdealPoint.val_zero, sub_eq_zero] at h
  have hx' : x.val = (1 + x.val) - 1 := by ring
  rw [hx']
  exact sub_mem (subset_adjoin _ _ h) (one_mem _)

end Torsion

variable {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosed Ω] [Algebra.IsSeparable ℚ_[p] Ω]

omit [Algebra.IsSeparable ℚ_[p] Ω] in

theorem unramifiedTower_le_adjoin_rootsOfUnity (m : ℕ) :
    unramifiedTower ℚ_[p] Ω m ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ (m + 1).factorial - 1) = 1} := by
  rw [unramifiedTower, adjoin_simple_le_iff]
  refine subset_adjoin _ _ ?_
  have h := (isPrimitiveRoot_unramifiedTowerRoot (K := ℚ_[p]) (Ω := Ω) m).pow_eq_one
  rwa [card_residueField] at h

theorem exists_le_adjoin_rootsOfUnity (L : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] L]
    [IsAbelianGalois ℚ_[p] L] :
    ∃ N : ℕ, 0 < N ∧ L ≤ adjoin ℚ_[p] {ζ : Ω | ζ ^ N = 1} := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower (irreducible_natCast_integer p)
    (isLubinTateSeries_multiplicativeLTPoly p) L
  have hM : 0 < p ^ (m + 1).factorial - 1 := Nat.sub_pos_of_lt
    (Nat.one_lt_pow (Nat.factorial_ne_zero _) hp.out.one_lt)
  refine ⟨p ^ (n + 1) * (p ^ (m + 1).factorial - 1),
    Nat.mul_pos (pow_pos hp.out.pos _) hM, h.trans (sup_le ?_ ?_)⟩
  · refine (lubinTateField_le_adjoin_rootsOfUnity p (n + 1)).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [pow_mul, hζ, one_pow]
  · refine (unramifiedTower_le_adjoin_rootsOfUnity p m).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [mul_comm, pow_mul, hζ, one_pow]

theorem coprime_pow_sub_one {k : ℕ} (hk : k ≠ 0) : (p ^ k - 1).Coprime p := by
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p hk
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.out.pos)] at h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)

omit [Algebra.IsSeparable ℚ_[p] Ω] in

theorem maximalUnramifiedExtension_eq_adjoin_rootsOfUnity :
    maximalUnramifiedExtension ℚ_[p] Ω =
      adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ζ ^ n = 1} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨m, hm⟩ := exists_mem_unramifiedTower hx
    have h1 := unramifiedTower_le_adjoin_rootsOfUnity p m hm
    refine adjoin.mono ℚ_[p] _ _ ?_ h1
    intro ζ hζ
    have hζ' : ζ ^ (p ^ (m + 1).factorial - 1) = 1 := hζ
    have hpos : 0 < p ^ (m + 1).factorial - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.factorial_ne_zero (m + 1)) hp.out.one_lt)
    exact ⟨p ^ (m + 1).factorial - 1, hpos,
      coprime_pow_sub_one p (Nat.factorial_ne_zero (m + 1)), hζ'⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hcop, hζn⟩
    have hφ : n.totient ≠ 0 := (Nat.totient_pos.2 hn).ne'
    obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := ℚ_[p]) (Ksep := Ω) hφ
    have hdvd : n ∣ p ^ n.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.out.pos)).1
        (Nat.ModEq.pow_totient hcop.symm).symm
    have hU := (isUnramifiedSubextension_adjoin hφ hξ).1
    rw [card_residueField] at hξ
    have : NeZero (p ^ n.totient - 1) := ⟨(Nat.sub_pos_of_lt
      (Nat.one_lt_pow hφ hp.out.one_lt)).ne'⟩
    obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (ξ := ζ) (by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, hζn, one_pow])
    rw [← hi]
    exact hU.le_maximalUnramifiedExtension (pow_mem (mem_adjoin_simple_self ℚ_[p] ξ) i)

theorem lubinTateLimit_le_adjoin_rootsOfUnity [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension ℚ_[p] Ω] :
    lubinTateLimit Ω (irreducible_natCast_integer p) ≤
      adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, ζ ^ (p ^ n) = 1} := by
  rw [lubinTateLimit_eq _ (isLubinTateSeries_multiplicativeLTPoly p)]
  exact iSup_le fun n => (lubinTateField_le_adjoin_rootsOfUnity p n).trans
    (adjoin.mono _ _ _ fun ζ (hζ : ζ ^ (p ^ n) = 1) =>
      show ∃ n : ℕ, ζ ^ (p ^ n) = 1 from ⟨n, hζ⟩)

variable (Ω) in

theorem maximalAbelianExtension_eq_adjoin_rootsOfUnity :
    maximalAbelianExtension ℚ_[p] Ω = adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1} := by
  have : IsSepClosure ℚ_[p] Ω := ⟨inferInstance, inferInstance⟩
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
    obtain ⟨N, hN, h⟩ := exists_le_adjoin_rootsOfUnity p L
    refine (h.trans (adjoin.mono _ _ _ ?_)) hyL
    intro ζ hζ
    exact ⟨N, hN, hζ⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hζn⟩
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
    have : NeZero (orderOf ζ) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
    have hζ : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
    have := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
    have := IsCyclotomicExtension.isAbelianGalois {orderOf ζ} ℚ_[p] ℚ_[p]⟮ζ⟯
    have : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := adjoin.finiteDimensional
      (IsIntegral.of_pow hn (by rw [hζn]; exact isIntegral_one))
    exact le_maximalAbelianExtension ℚ_[p]⟮ζ⟯ (mem_adjoin_simple_self ℚ_[p] ζ)

end Padic

end Padic

end GroundTheory.LocalField
