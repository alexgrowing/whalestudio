import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCardStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntCoeffPrimitiveGLCharacterStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegularStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularPrimitiveCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMulEsymmRootsPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfPeriodOfDvdSumPowersetCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularExponentOfSumSqEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement

noncomputable section

namespace GlobalTheory.CuspFormula

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.GoodCharsCompare

theorem esymm_mem_virt (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d k s : ℕ) :
    (fun x : GL (Fin d) F => (((Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)).map
      (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s) ∈ Virt ℂ ℂ (GL (Fin d) F) := by
  refine GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues _ _ _ (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F θ hθ d k) (fun x j _ => ?_) s
  rw [rootSum, ← Matrix.charpoly_map, ← Matrix.charpoly_map, Units.val_pow_eq_pow_val, Matrix.map_pow,
    GlobalTheory.T.roots_charpoly_pow_eq_map_pow, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp, map_pow, ← pow_mul, mul_comm]

theorem exists_regular (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ : GL (Fin d) F → ℂ) (hi : IsIrrChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ k : ℕ, (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) ∧
      ∀ x : GL (Fin d) F, χ x = (-1) ^ (d - 1) *
        psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
  classical
  have h := isCharacter_of_isIrreducibleCharacter_complex hi
  have hv : χ ∈ Virt ℂ ℂ (GL (Fin d) F) := AddSubgroup.subset_closure h
  obtain ⟨hval, -, hip, hcl⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  have hc := hcl (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one ℂ ℂ _ χ h).2.1
  have hr : Module.finrank F (Fin d → F) = d := by simp
  have hg := generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha, -⟩ := GlobalTheory.T.exists_int_coeff_primitive_GL_character F θ hθ d χ hd h hp
  have haa := sum_coef_mul_eq_pair F θ hθ d hd χ χ h h hp hp a a ha ha
  rw [GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed ℂ _ χ hi, mul_one] at haa
  have hinv : ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ d - 1] → a k = a l := by
    intro k l i hkl
    have := GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F (Fin d → F) θ _ hc hp (by rw [hr]; exact hd) k l i (by rw [hr]; exact hkl)
    rw [ha, ha] at this
    exact_mod_cast mul_right_cancel₀ hg this
  have hdvd : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro k s
    obtain ⟨m, hm⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card _ χ _ hv (esymm_mem_virt F θ hθ d k s)
    refine ⟨m, ?_⟩
    have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
    have key : ((∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, Nat.card F ^ i) : ℤ) : ℂ) * glCard F d =
        d * (m * glCard F d) := by
      push_cast
      rw [Finset.sum_mul]
      simp only [← ha, hip]
      rw [glCard, ← hm]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, hval, ← star_sum, Matrix.charpoly_toLin']
      by_cases hx : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
          LinearMap.charpoly (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = f ^ m
      · obtain ⟨f, m, hf, hirr, -, e⟩ := hx
        rw [Matrix.charpoly_toLin'] at e
        have hdeg : (f ^ m).natDegree = d := by rw [← e, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        have := GlobalTheory.T.natDegree_mul_esymm_roots_pow' F θ f m k s hf hirr
        rw [hdeg] at this
        rw [e, ← this, star_mul', star_natCast]
        ring
      · have := GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F _ _ hc hp (by rw [hr]; exact hd) _ hx
        rw [hval] at this
        simp [this]
    rw [← mul_assoc] at key
    exact_mod_cast mul_right_cancel₀ hg key
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_regular_exponent_of_sum_sq_eq' _ d a hq hd hinv (by simp only [sq]; exact_mod_cast haa)
    (GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' _ d a hq hd hinv hdvd)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h', hn⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular F θ hθ d k hd hk
  have hv' := AddSubgroup.subset_closure (k := {χ | IsChar ℂ ℂ χ}) h'
  have hsq : ((-1 : ℂ) ^ (d - 1)) * (-1) ^ (d - 1) = 1 := by rw [← mul_pow]; simp
  have hi' := ((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one _ _ hv' (by
    rw [hip] at hn
    rw [← glCard, ← hn]
    refine finsum_congr fun x => ?_
    rw [star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, hsq, one_mul])).2 h').1
  by_contra hne
  have h0 := GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible _ _ _ hi hi' (fun e => hne (congrFun e))
  have h1 := GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse F (Fin d → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1 _ hp
  rw [ha, hip] at h1
  rw [pair, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact hg (inv_eq_zero.1 h0)
  · have h2 : ∑ᶠ x : GL (Fin d) F, χ x * ((-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F)
        (Matrix.toLin' ((x⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) = (-1) ^ (d - 1) * (a k * glCard F d) := by
      have : Fintype (GL (Fin d) F) := Fintype.ofFinite _
      rw [← h1]
      simp only [finsum_eq_sum_of_fintype]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ hv' x, hval, star_mul', star_pow, star_neg, star_one]
      ring
    rw [h2] at h0
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (mul_ne_zero (by exact_mod_cast hk0) hg) h0

variable {g : ℕ} [Fact g.Prime]

theorem cuspVal_eq_psi (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    {x : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1) {k : ℕ} (hk : ω x = rootC (g ^ Fintype.card ι - 1) ^ k)
    (M : Matrix ι ι (ZMod g)) (hM : M.det ≠ 0) :
    cuspVal ω x M = (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar g →* ℂ) k) (ι → ZMod g) (Matrix.toLin' M) := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod g) (ω : Fbar g →* ℂ) k).1
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, m, hp, hm⟩ := hh
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) p (degree_pos_of_irreducible hp).ne'
    have hdeg := M.charpoly_natDegree_eq_dim
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [hm] at hdeg
        simp at hdeg
        omega
      · exact h
    have hf : M.charpoly = minpoly (ZMod g) y ^ m := by
      have h1 := minpoly.eq_of_irreducible hp hy
      have h2 : p.leadingCoeff ^ m = 1 := by
        rw [← leadingCoeff_pow, ← hm]
        exact M.charpoly_monic
      rw [← h1, mul_pow, ← C_pow, inv_pow, h2, inv_one, C_1, mul_one, hm]
    have hirr := minpoly.irreducible (isInt y)
    have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
      rw [hf, rootsBar_pow, Multiset.toFinset_nsmul _ _ hm0.ne']
    have hcard : (rootsBar M.charpoly).toFinset.card = dg y := by
      rw [hR, Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
    have he := fun z (hz : aeval z (minpoly (ZMod g) y) = 0) => GlobalTheory.T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace' (ZMod g) ι M _ z hirr hz
    rw [GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq (ZMod g) _ _ hs _ _ m _ (minpoly.monic (isInt y)) hirr hm0
      (by rw [Matrix.charpoly_toLin', hf]) (he y (minpoly.aeval _ _)), Nat.card_zmod]
    congr 1
    have e1 : rootSum (ω : Fbar g →* ℂ) k (minpoly (ZMod g) y) =
        ∑ z ∈ (rootsBar M.charpoly).toFinset, ω z ^ k := by
      rw [hR, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, (nodup_minpoly y).dedup]
      rfl
    rw [e1, Finset.sum_mul]
    convert Finset.sum_congr rfl (s₁ := (rootsBar M.charpoly).toFinset) fun z hz => ?_
    have hz1 := root_pow hM hp hm (Multiset.mem_toFinset.1 hz)
    have hz2 : aeval z (minpoly (ZMod g) y) = 0 := by
      rw [hR, Multiset.mem_toFinset] at hz
      exact (mem_rootsBar hirr.ne_zero).1 hz
    obtain ⟨a, ha⟩ := exists_log ω hd hz1
    have ht := Nat.eq_of_mul_eq_mul_left (dg_pos y) ((he z hz2).symm.trans (he y (minpoly.aeval _ _)))
    rw [labelChar_eq ω hd hx ha, hk, ha, ← pow_mul, ← pow_mul, mul_comm a k, ht]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcard]
  · rw [GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow (ZMod g) _ _ (fun e u => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ e u) (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse _ _ _ hs) (by simpa using hd),
      mul_zero]
    rintro ⟨f, m, -, hf, -, e⟩
    exact hh ⟨f, m, hf, by rw [← e, Matrix.charpoly_toLin']⟩

theorem exists_label {ω : Fbar g →*₀ ℂ} (hω : Function.Injective ω) {d : ℕ} (hd : 0 < d) {k : ℕ}
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * g ^ i ≡ k [MOD g ^ d - 1]) :
    ∃ x : Fbar g, x ^ (g ^ d - 1) = 1 ∧ ω x = rootC (g ^ d - 1) ^ k ∧ (minpoly (ZMod g) x).natDegree = d := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hprim := rootC_prim (g := g) hd
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (g ^ d - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  refine ⟨x, hx, hx', (GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL (ZMod g) d hd x (by simpa [Nat.card_zmod] using hx)).1.1 fun e he hed h => ?_⟩
  rw [Nat.card_zmod] at h
  have h1 := congrArg ω h
  rw [map_pow, hx', ← pow_mul] at h1
  have h0 := hprim.ne_zero (g_pow_sub_pos hd).ne'
  have hu : (Units.mk0 _ h0) ^ (k * g ^ e) = (Units.mk0 _ h0) ^ k := by
    ext; simpa using h1
  rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hprim.eq_orderOf] at hu
  exact hk e he hed hu

end GlobalTheory.CuspFormula
