import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGLStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem natCard_of_finrank {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) : Nat.card K = g ^ m := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]

private theorem frob_top {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (x : K) : x ^ g ^ m = x := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_of_finrank hm hK
  rw [← hc]
  exact FiniteField.pow_card x

private theorem aeval_pow_prime_pow_eq_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (j : ℕ) : aeval (x ^ g ^ j) Y = (aeval x Y) ^ g ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, pow_mul, ← ih, ← Polynomial.expand_aeval, ZMod.expand_card, map_pow]

private theorem conj_ne {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (a : ℕ) (ha : 0 < a) (ham : a < m) : (z : K) ^ g ^ a ≠ z := by
  intro h
  classical
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set F := IntermediateField.adjoin (ZMod g) {(z : K)} with hFdef
  have hF : Module.finrank (ZMod g) F = m := by
    rw [IntermediateField.adjoin.finrank hint, hz]
  have hfix : ∀ y ∈ F, y ^ g ^ a = y := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin (ZMod g) {(z : K)} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      exact hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show (aeval (z : K) p) ^ g ^ a = aeval (z : K) p
    rw [← aeval_pow_prime_pow_eq_pow, h]
  have hq : 1 < g ^ a := Nat.one_lt_pow ha.ne' hg.one_lt
  have hP0 : (X ^ (g ^ a) - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ (g ^ a) - X : K[X]))
    (Z := Finset.univ.map (Function.Embedding.subtype (· ∈ F))) (by
      intro y hy
      rw [Finset.map_val, Multiset.mem_map] at hy
      obtain ⟨⟨y, hyF⟩, -, rfl⟩ := hy
      rw [Polynomial.mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X]
      simp only [Function.Embedding.coe_subtype]
      rw [hfix y hyF, sub_self])
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_map, Finset.card_univ,
    Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hF] at hle
  have := Nat.pow_lt_pow_right hg.one_lt ham
  omega

private theorem conj_inj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (i j : ℕ) (hij : i < j) (hj : j < m) : (z : K) ^ g ^ i ≠ (z : K) ^ g ^ j := by
  intro h
  have key : ∀ x : K, (x ^ g ^ i) ^ g ^ (m - i) = x := by
    intro x
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact frob_top hm hK x
  apply conj_ne hm hK z hz (j - i) (by omega) (by omega)
  have hs : (z : K) ^ g ^ j = ((z : K) ^ g ^ (j - i)) ^ g ^ i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [hs] at h
  have h2 := congrArg (fun y => y ^ g ^ (m - i)) h
  simp only [key] at h2
  exact h2.symm

private theorem aeval_conj {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (hx : aeval x Y = 0) (j : ℕ) : aeval (x ^ g ^ j) Y = 0 := by
  rw [aeval_pow_prime_pow_eq_pow, hx, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]

private theorem roots_conj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (Y : (ZMod g)[X]) (hY : Irreducible Y) (hYm : Y.Monic)
    (hYd : Y.natDegree = m) (z : Kˣ) (hz : aeval (z : K) Y = 0) {L : Type} [Field L] (ι : K →+* L) :
    ((Y.map (algebraMap (ZMod g) K)).map ι).roots = (Multiset.range m).map fun j => ι ((z : K) ^ g ^ j) := by
  have hzm : (minpoly (ZMod g) (z : K)).natDegree = m := by
    rw [← minpoly.eq_of_irreducible_of_monic hY hz hYm, hYd]
  have hnd : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)).Nodup := by
    rw [Multiset.nodup_map_iff_inj_on (Multiset.nodup_range m)]
    intro i hi j hj hij
    simp only [Multiset.mem_range] at hi hj
    have h' : (z : K) ^ g ^ i = (z : K) ^ g ^ j := ι.injective hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd h' (conj_inj hm hK z hzm i j h hj)
    · exact h
    · exact absurd h'.symm (conj_inj hm hK z hzm j i h hi)
  have hP0 : ((Y.map (algebraMap (ZMod g) K)).map ι) ≠ 0 := ((hYm.map _).map _).ne_zero
  have hle : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)) ≤
      ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    rw [mem_roots hP0, IsRoot, eval_map, eval₂_map, ← Polynomial.hom_eval₂, ← aeval_def,
      aeval_conj Y _ hz j, map_zero]
  have hdeg : ((Y.map (algebraMap (ZMod g) K)).map ι).natDegree = m := by
    rw [natDegree_map, natDegree_map, hYd]
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [Multiset.card_map, Multiset.card_range, ← hdeg]
  exact card_roots' _

private theorem false_of_reg_of_mul_pow_modEq {g m c i j : ℕ} (hg : 0 < g) (hc : Reg g m c) (hij : i < j) (hj : j < m)
    (h : c * g ^ i ≡ c * g ^ j [MOD g ^ m - 1]) : False := by
  have hone : g ^ m ≡ 1 [MOD g ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  have h2 := h.mul_right (g ^ (m - i))
  have e1 : c * g ^ i * g ^ (m - i) = c * g ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have e2 : c * g ^ j * g ^ (m - i) = c * g ^ (j - i) * g ^ m := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e1, e2] at h2
  have h3 : c * g ^ m ≡ c [MOD g ^ m - 1] := by simpa using hone.mul_left c
  have h4 : c * g ^ (j - i) * g ^ m ≡ c * g ^ (j - i) [MOD g ^ m - 1] := by
    simpa using hone.mul_left (c * g ^ (j - i))
  exact hc (j - i) (by omega) (by omega) (h4.symm.trans (h2.symm.trans h3))

private theorem regular_character_of_pow {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K 𝔨 : Type} [Field K] [Algebra (ZMod g) K] [Field 𝔨]
    (hK : Module.finrank (ZMod g) K = m) (ι : K →+* 𝔨) (Θ : 𝔨 →* ℂ) (hΘ : Inj Θ) (c : ℕ) (hc : Reg g m c) :
    GlobalTheory.Published.IsRegularChar g m ((Units.map (Θ.comp ι.toMonoidHom)) ^ c : Kˣ →* ℂˣ) := by
  intro i j hi hj hij
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = g ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, natCard_of_finrank hm hK]
  have hv := DFunLike.congr_fun hij ζ
  simp only [MonoidHom.pow_apply, ← pow_mul] at hv
  rw [← map_pow, ← map_pow] at hv
  have hv' : Θ (ι ((ζ ^ (c * g ^ i) : Kˣ) : K)) = Θ (ι ((ζ ^ (c * g ^ j) : Kˣ) : K)) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hv
  have h1 := hΘ _ _ (by simp) (by simp) hv'
  have h2 : ζ ^ (c * g ^ i) = ζ ^ (c * g ^ j) := Units.ext (ι.injective h1)
  rw [pow_eq_pow_iff_modEq, hord] at h2
  rcases lt_trichotomy i j with h | h | h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hj h2).elim
  · exact h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hi h2.symm).elim

theorem UpperTheory.Gal.InertialTypesAlt.nameOf :
    NameOf := by
  intro g _ m hm F K 𝔨 _ _ _ _ _ hK r e ι Θ hΘ c hc
  refine ⟨(Units.map (Θ.comp ι.toMonoidHom)) ^ c, ?_, regular_character_of_pow hm hK ι Θ hΘ c hc, ?_⟩
  · intro u
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  · intro τ hτ y hy z hz
    set Y : (ZMod g)[X] := (y : Matrix (Fin m) (Fin m) (ZMod g)).charpoly with hYdef
    have hYm : Y.Monic := Matrix.charpoly_monic _
    have hYd : Y.natDegree = m := by
      rw [hYdef, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    let γ : GL (Fin m) F := Matrix.GeneralLinearGroup.map r.symm.toRingHom y
    have hyγ : Matrix.GeneralLinearGroup.map r.toRingHom γ = y := by
      ext i j
      simp [γ]
    have hγc : (γ : Matrix (Fin m) (Fin m) F).charpoly = Y.map r.symm.toRingHom := by
      rw [show (γ : Matrix (Fin m) (Fin m) F) = (y : Matrix (Fin m) (Fin m) (ZMod g)).map r.symm.toRingHom
        from rfl, Matrix.charpoly_map]
    have hirr : Irreducible (LinearMap.charpoly (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) F))) := by
      rw [Matrix.charpoly_toLin', hγc]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv r.symm)).mpr hy
    rw [← hyγ, hτ γ]
    delta cusp psiG
    congr 1
    refine (GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin m → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F (Θ.comp e) c).1 _ hirr).trans ?_
    rw [Matrix.charpoly_toLin', hγc]
    delta GlobalTheory.CuspGL.rootSum
    rw [Polynomial.map_map]
    have hP : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).Splits :=
      IsAlgClosed.splits _
    have hroots : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e =
        ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
      rw [← hP.roots_map e, Polynomial.map_map, Polynomial.map_map]
      congr 2
      exact Subsingleton.elim _ _
    have hre : ((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map
        fun α => (Θ.comp e) α ^ c) =
        (((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e).map
        fun β => Θ β ^ c) := by
      rw [Multiset.map_map]
      rfl
    rw [hre, hroots, roots_conj hm hK Y hy hYm hYd z hz ι, Multiset.map_map,
      Finset.sum_eq_multiset_sum, Finset.range_val]
    apply congrArg
    apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp_apply]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
