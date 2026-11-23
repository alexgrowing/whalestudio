import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntCoeffPrimitiveGLCharacterStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OrthogonalIntVectorsNotAgreeOnRegular
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonalityStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

open Polynomial in
theorem _root_.GlobalTheory.CuspGL.isCharacter_of_isIrreducibleCharacter_complex {G : Type} [Group G] {χ : G → ℂ} (h : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ := by
  obtain ⟨n, ρ, -, hρ⟩ := h
  exact ⟨n, ρ, hρ⟩

open Polynomial in
theorem _root_.GlobalTheory.CuspGL.generalLinearGroupCardComplex_finiteField_ne_zero (F : Type) [Field F] [Finite F] (d : ℕ) : _root_.GlobalTheory.CuspGL.glCard F d ≠ 0 := by
  unfold _root_.GlobalTheory.CuspGL.glCard
  exact_mod_cast Nat.card_pos.ne'

open Polynomial in

theorem _root_.GlobalTheory.CuspGL.sum_coef_mul_eq_pair (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ χ' : GL (Fin d) F → ℂ) (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) (h' : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ')
    (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ)) (hp' : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ')) (a b : ℕ → ℤ)
    (ha : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ) (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = a k * _root_.GlobalTheory.CuspGL.glCard F d)
    (hb : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ') (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = b k * _root_.GlobalTheory.CuspGL.glCard F d) :
    ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k * b k : ℤ) : ℂ) = d * _root_.GlobalTheory.BI.pair χ χ' := by
  classical
  letI : Fintype (GL (Fin d) F) := Fintype.ofFinite _
  have hN : _root_.GlobalTheory.CuspGL.glCard F d ≠ 0 := _root_.GlobalTheory.CuspGL.generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  obtain ⟨h1, -, h3, h4⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ
  obtain ⟨h1', -, -, h4'⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ'
  have hinv' := h4' (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ' h').2.1
  set M : ℕ → Module.End F (Fin d → F) → ℂ := fun k =>
    _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) with hMdef

  have hexp : ∀ x : GL (Fin d) F, (d : ℂ) * χ' x =
      ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) * M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
    intro x
    have hu : IsUnit (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) :=
      x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin d))
    have := _root_.GlobalTheory.CuspGL.expand_primitive F (Fin d → F) θ hθ _ hinv' hp'
      (by rw [hfr]; exact hd) _ hu
    rw [hfr, h1'] at this
    simp only [hb] at this
    apply mul_left_cancel₀ hN
    rw [Finset.mul_sum, ← mul_assoc, this]
    refine Finset.sum_congr rfl fun k _ => by simp only [M]; ring

  have hMk : ∀ k, ∑ x : GL (Fin d) F, χ x * star (M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) =
      a k * _root_.GlobalTheory.CuspGL.glCard F d := by
    intro k
    rw [← ha k, ← _root_.GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq F (Fin d → F) _
      (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1 _ hp, h3,
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ => by rw [h1]
  have hpair : ∑ x : GL (Fin d) F, χ x * star (χ' x) =
      _root_.GlobalTheory.CuspGL.glCard F d * _root_.GlobalTheory.BI.pair χ χ' := by
    unfold _root_.GlobalTheory.BI.pair _root_.GlobalTheory.CuspGL.glCard
    have hN' : ((Nat.card (GL (Fin d) F) : ℂ)) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [_root_.GlobalTheory.CuspGL.star_virt_eq_inv _ _ (_root_.GlobalTheory.BI.isChar_mem_virt_complex h') x]
  have hmain : (d : ℂ) * ∑ x : GL (Fin d) F, χ x * star (χ' x) =
      ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) *
        ∑ x : GL (Fin d) F, χ x * star (M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := congrArg star (hexp x)
    rw [star_mul', star_natCast, star_sum] at this
    rw [mul_left_comm, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', star_intCast]
    ring
  rw [hpair] at hmain
  simp only [hMk] at hmain
  apply mul_left_cancel₀ hN
  push_cast
  have hre : ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) * (a k * _root_.GlobalTheory.CuspGL.glCard F d) =
      _root_.GlobalTheory.CuspGL.glCard F d * ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ) * b k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hre] at hmain
  linear_combination -hmain

open Polynomial in
private theorem charpoly_toLin'' {F : Type} [Field F] {d : ℕ} (M : Matrix (Fin d) (Fin d) F) :
    (Matrix.toLin' M).charpoly = M.charpoly := by
  rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun F (Fin d)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

open Polynomial in
private theorem sum_range_apply_mul_mod_eq_of_coprime {m u : ℕ} (hu : Nat.Coprime u m) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range m, c (k * u % m) = ∑ k ∈ Finset.range m, c k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hinj : ∀ a ∈ Finset.range m, ∀ b ∈ Finset.range m, a * u % m = b * u % m → a = b := by
    intro a ha b hb hab
    have h := Nat.ModEq.cancel_right_of_coprime (c := u) (by rw [Nat.gcd_comm]; exact hu) hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at h
  refine Finset.sum_nbij (fun k => k * u % m) (fun a _ => Finset.mem_range.2 (Nat.mod_lt _ hm))
    (fun a ha b hb hab => hinj a ha b hb hab) ?_ (fun _ _ => rfl)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range m) (t := Finset.range m)
    (fun k _ => k * u % m) (fun a _ => Finset.mem_range.2 (Nat.mod_lt _ hm))
    (fun a b ha hb hab => hinj a ha b hb hab) le_rfl b hb
  exact ⟨a, ha, rfl⟩

open Polynomial in
private theorem character_elliptic_eq_coeff_sum_lemma (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ : GL (Fin d) F → ℂ) (hχ : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ)
    (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ)) (a : ℕ → ℤ)
    (ha : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ)
      (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g)) =
        a k * _root_.GlobalTheory.CuspGL.glCard F d)
    {ζ : AlgebraicClosure F} (hω : IsPrimitiveRoot (θ ζ) (Nat.card F ^ d - 1)) (j : ℕ)
    (x : GL (Fin d) F) (hx : (x : Matrix (Fin d) (Fin d) F).charpoly = minpoly F (ζ ^ j))
    (hdeg : (minpoly F (ζ ^ j)).natDegree = d) :
    χ x = ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ) * θ ζ ^ (j * k) := by
  classical
  set q := Nat.card F with hqdef
  set m := q ^ d - 1 with hmdef
  set ω := θ ζ with hωdef
  have hN : _root_.GlobalTheory.CuspGL.glCard F d ≠ 0 := by
    unfold _root_.GlobalTheory.CuspGL.glCard
    exact_mod_cast Nat.card_pos.ne'
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hcls : ∀ g y : GL (Fin d) F, χ (y⁻¹ * g * y) = χ g :=
    (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  obtain ⟨h1, -, -, h4⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ
  have hinv := h4 hcls
  have hu : IsUnit (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) :=
    x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin d))
  have hexp := _root_.GlobalTheory.CuspGL.expand_primitive F (Fin d → F) θ hθ _ hinv hp
    (by rw [hfr]; exact hd) _ hu
  rw [hfr, h1] at hexp
  simp only [ha] at hexp
  have hirr : Irreducible (LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
    rw [charpoly_toLin'', hx]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  have hM : ∀ k, _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)
      (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = ∑ i ∈ Finset.range d, ω ^ (j * q ^ i * k) := by
    intro k
    rw [_root_.GlobalTheory.CuspGL.psi_of_irreducible_charpoly F (Fin d → F) _
      (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1 _ hirr, charpoly_toLin'', hx]
    unfold _root_.GlobalTheory.CuspGL.rootSum
    rw [_root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, hdeg, Multiset.map_map, Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun i _ => ?_)
    simp only [Function.comp_apply, map_pow, ← pow_mul, hωdef]
    rw [hqdef]
    try ring
  have hmodω : ∀ s t : ℕ, s % m = t % m → ω ^ s = ω ^ t := fun s t hst => by
    rw [← pow_mod_orderOf ω s, ← pow_mod_orderOf ω t, ← hω.eq_orderOf, hst]
  have hcop : Nat.Coprime q m := by
    have h1q : 1 ≤ q ^ d := Nat.one_le_pow _ _ Nat.card_pos
    have : Nat.Coprime (q ^ d) m := by
      rw [hmdef, Nat.coprime_self_sub_right h1q]
      exact Nat.coprime_one_right _
    exact this.coprime_dvd_left (dvd_pow_self q hd.ne')
  have hinner : ∀ i, ∑ k ∈ Finset.range m, (a k : ℂ) * ω ^ (j * q ^ i * k) =
      ∑ k ∈ Finset.range m, (a k : ℂ) * ω ^ (j * k) := by
    intro i
    rw [← sum_range_apply_mul_mod_eq_of_coprime (hcop.pow_left i) (fun k => (a k : ℂ) * ω ^ (j * k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have haeq : a k = a (k * q ^ i % m) := by
      have := _root_.GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq F (Fin d → F) θ _ hinv hp
        (by rw [hfr]; exact hd) k (k * q ^ i % m) i (by rw [hfr]; exact (Nat.mod_modEq _ _).symm)
      rw [ha, ha] at this
      exact_mod_cast mul_right_cancel₀ hN this
    rw [← haeq]
    congr 1
    apply hmodω
    rw [show j * q ^ i * k = j * (k * q ^ i) by ring]
    exact (Nat.ModEq.mul_left j (Nat.mod_modEq (k * q ^ i) m)).symm
  have hsum : ∑ k ∈ Finset.range m, ((a k : ℂ) * _root_.GlobalTheory.CuspGL.glCard F d) *
      _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F)
        (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) =
      _root_.GlobalTheory.CuspGL.glCard F d * ((d : ℂ) * ∑ k ∈ Finset.range m, (a k : ℂ) * ω ^ (j * k)) := by
    simp_rw [hM]
    calc _ = _root_.GlobalTheory.CuspGL.glCard F d * ∑ i ∈ Finset.range d,
          ∑ k ∈ Finset.range m, (a k : ℂ) * ω ^ (j * q ^ i * k) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          simp_rw [hinner]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum] at hexp
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  apply mul_left_cancel₀ (mul_ne_zero hN hd0)
  linear_combination hexp

open Polynomial in

theorem _root_.GlobalTheory.CuspGL.eq_of_isPrimitive_of_eq_on_elliptic (F : Type) [Field F] [Finite F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ)
    (hd : 0 < d) (hi : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) (hi' : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ') (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ))
    (hp' : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ'))
    (he : ∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) :
    χ = χ' := by
  classical
  by_contra hne
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.CuspGL.TeichEmb.exists_teichmuller F
  have hc := _root_.GlobalTheory.CuspGL.isCharacter_of_isIrreducibleCharacter_complex hi
  have hc' := _root_.GlobalTheory.CuspGL.isCharacter_of_isIrreducibleCharacter_complex hi'
  obtain ⟨a, ha, hdegA⟩ := _root_.GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive F θ hθ d χ hd hc hp
  obtain ⟨b, hb, hdegB⟩ := _root_.GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive F θ hθ d χ' hd hc' hp'
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hqd : 2 ≤ Nat.card F ^ d := le_trans hq2 (Nat.le_self_pow hd.ne' _)
  have hm : 0 < Nat.card F ^ d - 1 := by omega
  have hself := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ _ χ hi
  have hself' := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ _ χ' hi'
  have hsa : ∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k ^ 2 = d := by
    have := _root_.GlobalTheory.CuspGL.sum_coef_mul_eq_pair F θ hθ d hd χ χ hc hc hp hp a a ha ha
    rw [hself, mul_one] at this
    simp_rw [sq]
    exact_mod_cast this
  have hsb : ∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k ^ 2 = d := by
    have := _root_.GlobalTheory.CuspGL.sum_coef_mul_eq_pair F θ hθ d hd χ' χ' hc' hc' hp' hp' b b hb hb
    rw [hself', mul_one] at this
    simp_rw [sq]
    exact_mod_cast this
  have hab : ∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k * b k = 0 := by
    have := _root_.GlobalTheory.CuspGL.sum_coef_mul_eq_pair F θ hθ d hd χ χ' hc hc' hp hp' a b ha hb
    rw [_root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne _ χ χ' hi hi' hne, mul_zero] at this
    exact_mod_cast this

  have hdegpos : ∀ ψ : GL (Fin d) F → ℂ, _root_.GlobalTheory.BI.IsChar ℂ ℂ ψ →
      _root_.GlobalTheory.BI.pair ψ ψ = 1 → ∃ n : ℕ, 0 < n ∧ ψ 1 = n := by
    intro ψ hψ h1
    obtain ⟨n, hn, hn0⟩ := (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ ψ hψ).2.2
    refine ⟨n, Nat.pos_of_ne_zero fun h0 => ?_, hn⟩
    have := hn0 h0
    subst this
    unfold _root_.GlobalTheory.BI.pair at h1
    simp at h1
  obtain ⟨n, hn, hn1⟩ := hdegpos χ hc hself
  obtain ⟨n', hn', hn1'⟩ := hdegpos χ' hc' hself'
  set P : ℤ := ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℤ) ^ i) with hP
  have hA : ((d * n : ℕ) : ℤ) = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k) * P := by
    rw [hn1] at hdegA
    have h : (((d * n : ℕ) : ℤ) : ℂ) = (((∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k) * P : ℤ) : ℂ) := by
      rw [hP]
      push_cast
      exact hdegA
    exact_mod_cast h
  have hB : ((d * n' : ℕ) : ℤ) = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k) * P := by
    rw [hn1'] at hdegB
    have h : (((d * n' : ℕ) : ℤ) : ℂ) = (((∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k) * P : ℤ) : ℂ) := by
      rw [hP]
      push_cast
      exact hdegB
    exact_mod_cast h
  have hpos : 0 < (∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k) *
      ∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k := by
    by_contra hle
    push_neg at hle
    have h0 : (0 : ℤ) < ((d * n : ℕ) : ℤ) * ((d * n' : ℕ) : ℤ) := by positivity
    rw [hA, hB] at h0
    have : (∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k) * P *
        ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k) * P) =
        ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k) *
          ∑ k ∈ Finset.range (Nat.card F ^ d - 1), b k) * (P * P) := by ring
    rw [this] at h0
    exact absurd h0 (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hle (mul_self_nonneg P)))
  obtain ⟨⟨ζ, hζ, hω⟩, -⟩ := _root_.GlobalTheory.CuspGL.torus_orthogonality F θ hθ d hd
  refine _root_.GlobalTheory.CuspGL.orthogonal_int_vectors_not_agree_on_regular (Nat.card F) d (θ ζ) a b hq2 hd hω hsa hsb hab hpos ?_
  intro j hj
  have hα : (ζ ^ j) ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨hiff, hex⟩ := _root_.GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic F d hd (ζ ^ j) hα
  have hreg : ∀ e : ℕ, 0 < e → e < d → (ζ ^ j) ^ Nat.card F ^ e ≠ ζ ^ j := by
    intro e he0 hed heq
    apply hj e he0 hed
    rw [← pow_mul] at heq
    have h' : ζ ^ (j * Nat.card F ^ e % (Nat.card F ^ d - 1)) = ζ ^ (j % (Nat.card F ^ d - 1)) := by
      rw [hζ.eq_orderOf, pow_mod_orderOf, pow_mod_orderOf, heq]
    exact hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) h'
  have hdeg := hiff.1 hreg
  obtain ⟨x, hx⟩ := hex hdeg
  have hirr : Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) := by
    rw [hx]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  rw [← character_elliptic_eq_coeff_sum_lemma F θ hθ d hd χ hc hp a ha hω j x hx hdeg,
    ← character_elliptic_eq_coeff_sum_lemma F θ hθ d hd χ' hc' hp' b hb hω j x hx hdeg, he x hirr]

end GlobalTheory.CuspGL
