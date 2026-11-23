import Mathlib
open NumberField

namespace PositivityTheory.Xgn.CharZeroFreeModule
open Polynomial

section chi
variable (k : Type) [Field k]

noncomputable def chi (M : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] : k[X] :=
  (Algebra.lsmul k k M (X : k[X])).charpoly

variable {k}
variable {M N : Type} [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module k[X] N]
    [IsScalarTower k k[X] N] [FiniteDimensional k N]

theorem chi_monic : (chi k M).Monic := LinearMap.charpoly_monic _

theorem chi_natDegree : (chi k M).natDegree = Module.finrank k M :=
  LinearMap.charpoly_natDegree _

theorem chi_smul (m : M) : chi k M • m = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lsmul k k M (X : k[X]))
  rw [Polynomial.aeval_algHom_apply, aeval_X_left_apply] at h
  exact congrArg (fun f => f m) h

theorem chi_equiv (e : M ≃ₗ[k[X]] N) : chi k M = chi k N := by
  unfold chi
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext n
  simp [LinearEquiv.conj_apply]

theorem chi_prod : chi k (M × N) = chi k M * chi k N := by
  unfold chi
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem chi_simple [IsSimpleModule k[X] M] :
    Irreducible (chi k M) ∧ Nonempty (M ≃ₗ[k[X]] k[X] ⧸ Ideal.span {chi k M}) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule k[X] M›
  obtain ⟨q, rfl⟩ : ∃ q, I = Ideal.span {q} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have hd : q ∣ chi k M := by
    have h := congrArg e (chi_smul (k := k) (e.symm 1))
    rw [map_smul, e.apply_symm_apply, map_zero, Algebra.smul_def, mul_one] at h
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h0 : chi k M ≠ 0 := chi_monic.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact h0 (zero_dvd_iff.mp hd)
  have hdeg : (chi k M).natDegree = q.natDegree := by
    rw [chi_natDegree, (e.restrictScalars k).finrank_eq, finrank_quotient_span_eq_natDegree]
  have ha : Associated q (chi k M) :=
    associated_of_dvd_of_natDegree_le hd h0 hdeg.le
  have hp : Prime q := (Ideal.span_singleton_prime hq0).mp hI.isPrime
  refine ⟨ha.irreducible hp.irreducible, ⟨e.trans (Submodule.quotEquivOfEq _ _ ?_)⟩⟩
  exact Ideal.span_singleton_eq_span_singleton.mpr ha

instance subFin (T : Submodule k[X] M) : FiniteDimensional k T :=
  Module.Finite.of_injective (T.subtype.restrictScalars k) T.injective_subtype

omit [Module k M] [IsScalarTower k k[X] M] [FiniteDimensional k M] in
theorem exists_split [IsSemisimpleModule k[X] M] (T : Submodule k[X] M) :
    ∃ T' : Submodule k[X] M, Nonempty (M ≃ₗ[k[X]] T × T') := by
  obtain ⟨T', h⟩ := exists_isCompl T
  exact ⟨T', ⟨(Submodule.prodEquivOfIsCompl _ _ h).symm⟩⟩

theorem finrank_lt_of_split {S T : Submodule k[X] M} [IsSimpleModule k[X] S]
    (e : M ≃ₗ[k[X]] S × T) : Module.finrank k T < Module.finrank k M := by
  haveI : Nontrivial S := IsSimpleModule.nontrivial k[X] S
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_prod]
  have : 0 < Module.finrank k S := Module.finrank_pos
  omega

end chi

theorem exists_simple_of_dvd {k : Type} [Field k] (p : k[X]) (hp : Irreducible p) (hm : p.Monic)
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] [IsSemisimpleModule k[X] M],
    Module.finrank k M = n → p ∣ chi k M →
    ∃ T : Submodule k[X] M, IsSimpleModule k[X] T ∧ chi k T = p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ _ hn hd
  rcases subsingleton_or_nontrivial M with hM | hM
  · exfalso
    have h1 : chi k M = 1 := by
      rw [← chi_monic.natDegree_eq_zero, chi_natDegree]
      exact Module.finrank_zero_of_subsingleton
    rw [h1] at hd
    exact hp.not_isUnit (isUnit_of_dvd_one hd)
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule k[X] M
  obtain ⟨T, ⟨e⟩⟩ := exists_split S
  rw [chi_equiv e, chi_prod] at hd
  rcases hp.prime.dvd_or_dvd hd with h | h
  · exact ⟨S, hS, (eq_of_monic_of_associated hm chi_monic
      (hp.associated_of_dvd chi_simple.1 h)).symm⟩
  · obtain ⟨U, hU, hc⟩ := ih _ (hn ▸ finrank_lt_of_split e) T rfl h
    have e' := U.equivMapOfInjective T.subtype T.injective_subtype
    exact ⟨U.map T.subtype, IsSimpleModule.congr e'.symm, (chi_equiv e').symm.trans hc⟩

theorem equiv_of_chi_eq {k : Type} [Field k]
    (n : ℕ) : ∀ (M N : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] [IsSemisimpleModule k[X] M]
    [AddCommGroup N] [Module k N] [Module k[X] N]
    [IsScalarTower k k[X] N] [FiniteDimensional k N] [IsSemisimpleModule k[X] N],
    Module.finrank k M = n → chi k M = chi k N → Nonempty (M ≃ₗ[k[X]] N) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ _ _ hn hc
  rcases subsingleton_or_nontrivial M with hM | hM
  · have h : Module.finrank k N = 0 := by
      rw [← chi_natDegree, ← hc, chi_natDegree]
      exact Module.finrank_zero_of_subsingleton
    haveI : Subsingleton N := Module.finrank_zero_iff.mp h
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule k[X] M
  obtain ⟨T, ⟨e⟩⟩ := exists_split S
  have h1 : chi k M = chi k S * chi k T := by rw [chi_equiv e, chi_prod]
  obtain ⟨S', hS', hc'⟩ := exists_simple_of_dvd (chi k S) chi_simple.1 chi_monic _ N rfl
    ⟨_, hc.symm.trans h1⟩
  obtain ⟨T', ⟨e'⟩⟩ := exists_split S'
  have h2 : chi k N = chi k S' * chi k T' := by rw [chi_equiv e', chi_prod]
  have h3 : chi k T = chi k T' := by
    rw [h1, h2, hc'] at hc
    exact mul_left_cancel₀ chi_monic.ne_zero hc
  obtain ⟨f⟩ := ih _ (hn ▸ finrank_lt_of_split e) T T' rfl h3
  obtain ⟨g⟩ := (chi_simple (k := k) (M := S)).2
  obtain ⟨g'⟩ := (chi_simple (k := k) (M := S')).2
  rw [hc'] at g'
  exact ⟨e.trans (((g.trans g'.symm).prodCongr f).trans e'.symm)⟩

theorem chi_aeval {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : Module.End k V) : chi k (Module.AEval' f) = f.charpoly := by
  unfold chi
  rw [← LinearEquiv.charpoly_conj (Module.AEval'.of f) f]
  congr 1
  ext v
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective v
  simp [LinearEquiv.conj_apply, Module.AEval'.X_smul_of]

theorem conj_of_charpoly_eq {k V W : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (f : Module.End k V) (g : Module.End k W) (hf : f.IsSemisimple) (hg : g.IsSemisimple)
    (h : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[k] W, ∀ v, e (f v) = g (e v) := by
  haveI : IsSemisimpleModule k[X] (Module.AEval' f) := hf
  haveI : IsSemisimpleModule k[X] (Module.AEval' g) := hg
  obtain ⟨e⟩ := equiv_of_chi_eq (k := k) _ (Module.AEval' f) (Module.AEval' g) rfl
    (by rw [chi_aeval, chi_aeval, h])
  refine ⟨(Module.AEval'.of f).trans ((e.restrictScalars k).trans (Module.AEval'.of g).symm),
    fun v => ?_⟩
  apply (Module.AEval'.of g).injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.restrictScalars_apply]
  rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, map_smul,
    LinearEquiv.apply_symm_apply]

theorem charpoly_compLeft {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.End k V) (r : ℕ) :
    LinearMap.charpoly (f.compLeft (Fin r)) = f.charpoly ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, ← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  | succ r ih =>
    rw [pow_succ', ← ih, ← LinearMap.charpoly_prodMap,
      ← LinearEquiv.charpoly_conj (Fin.consLinearEquiv k (fun _ : Fin (r + 1) => V))]
    congr 1
    refine LinearMap.ext fun v => funext fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [LinearEquiv.conj_apply]
    · simp [LinearEquiv.conj_apply, Fin.tail]

theorem aeval_rho {R k W : Type} [CommRing R] [Field k] [AddCommGroup W] [Module k W]
    (ρ : R →+* Module.End k W) (a : R) (P : ℤ[X]) :
    aeval (ρ a) (P.map (Int.castRingHom k)) = ρ (aeval a P) := by
  have h := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a P
  have h2 := Polynomial.aeval_map_algebraMap k (ρ a) P
  exact h2.trans h

theorem rho_semisimple {E : Type} [Field E] [NumberField E] {k W : Type} [Field k] [CharZero k]
    [AddCommGroup W] [Module k W] (ρ : 𝓞 E →+* Module.End k W) (a : 𝓞 E) :
    (ρ a).IsSemisimple := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi
  have h2 : ((minpoly ℤ a).map (algebraMap ℤ ℚ)).Separable := by
    rw [← h1]
    exact (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable
  have h3 : ((minpoly ℤ a).map (Int.castRingHom k)).Separable := by
    have := h2.map (f := algebraMap ℚ k)
    rw [Polynomial.map_map] at this
    rwa [RingHom.eq_intCast' ((algebraMap ℚ k).comp (algebraMap ℤ ℚ))] at this
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero h3.squarefree ?_
  rw [aeval_rho, minpoly.aeval, map_zero]

theorem exists_gen (E : Type) [Field E] [NumberField E] :
    ∃ a : 𝓞 E, ∀ b : 𝓞 E, ∃ (N : ℤ) (P : ℤ[X]), N ≠ 0 ∧ N • b = aeval a P := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have halg : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y • α := ⟨⟨y • α, hint⟩, rfl⟩
  refine ⟨a, fun b => ?_⟩
  have hb : (b : E) ∈ Algebra.adjoin ℚ {α} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨Q, hQ⟩ := hb
  have hQ' : aeval (y • α) (Q.comp (C (y : ℚ)⁻¹ * X)) = (b : E) := by
    have hy' : (y : E) ≠ 0 := Int.cast_ne_zero.mpr hy
    rw [aeval_comp]
    simp only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast, zsmul_eq_mul]
    rw [inv_mul_cancel_left₀ hy']
    exact hQ
  obtain ⟨N, hN, hs⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
    (Q.comp (C (y : ℚ)⁻¹ * X))
  refine ⟨N, IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q.comp (C (y : ℚ)⁻¹ * X)),
    nonZeroDivisors.ne_zero hN, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap ℚ, hs, ha]
  simp only [map_zsmul]
  congr 1
  exact hQ'.symm

end PositivityTheory.Xgn.CharZeroFreeModule

open PositivityTheory.Xgn.CharZeroFreeModule in
theorem PositivityTheory.Xgn.char_zero_free_module : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  intro E _ _ k W _ _ _ _ _ r ρ hρ
  obtain ⟨a, ha⟩ := exists_gen E
  let ρ0 : 𝓞 E →+* Module.End k (Fin r → TensorProduct ℤ k (𝓞 E)) :=
    (Algebra.lsmul k k (Fin r → TensorProduct ℤ k (𝓞 E)) :
      TensorProduct ℤ k (𝓞 E) →ₐ[k] _).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := k) (B := 𝓞 E)).toRingHom
  have hρ0 : ∀ b v i, ρ0 b v i = ((1 : k) ⊗ₜ[ℤ] b) * v i := fun _ _ _ => rfl
  have hc : (ρ0 a).charpoly = (ρ a).charpoly := by
    have h1 : ρ0 a = LinearMap.compLeft
        (LinearMap.baseChange k (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E))) (Fin r) := by
      rw [Algebra.baseChange_lmul]
      rfl
    rw [hρ a, h1, charpoly_compLeft, LinearMap.charpoly_baseChange]
    rfl
  obtain ⟨e, he⟩ := conj_of_charpoly_eq _ _ (rho_semisimple ρ0 a) (rho_semisimple ρ a) hc
  have hp : ∀ (P : Polynomial ℤ) v, e (ρ0 (Polynomial.aeval a P) v) =
      ρ (Polynomial.aeval a P) (e v) := by
    intro P
    induction P using Polynomial.induction_on with
    | C c =>
      intro v
      rw [Polynomial.aeval_C, eq_intCast, map_intCast, map_intCast, Module.End.intCast_apply,
        Module.End.intCast_apply, map_zsmul]
    | add p q hp hq => intro v; simp [hp, hq]
    | monomial n c h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval a), Polynomial.aeval_X, map_mul ρ0,
        map_mul ρ, Module.End.mul_apply, Module.End.mul_apply, h, he]
  have hb : ∀ b v, e (ρ0 b v) = ρ b (e v) := by
    intro b v
    obtain ⟨N, P, hN, h⟩ := ha b
    have := hp P v
    rw [← h, map_zsmul, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul,
      ← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k] at this
    exact smul_right_injective W (Int.cast_ne_zero.mpr hN) this
  let B := ((Pi.basis fun _ : Fin r => (RingOfIntegers.basis E).baseChange k).reindex
    (Equiv.sigmaEquivProd _ _)).map e
  have hB : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (e (Pi.single q.1 1))) = B := by
    funext ⟨i, j⟩
    simp only [B, Module.Basis.map_apply, Module.Basis.reindex_apply]
    rw [← hb]
    congr 1
    funext l
    rw [hρ0]
    simp only [Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Module.Basis.baseChange_apply]
    by_cases h : l = i
    · subst h; simp
    · simp [h]
  refine ⟨fun i => e (Pi.single i 1), ?_, ?_⟩
  · rw [hB]; exact B.linearIndependent
  · rw [hB]; exact B.span_eq
