import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quotSpanNat_mk_eq_sum {S : Type} [CommRing S] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ S)
    (n : ℕ) [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (s : S) :
    Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s =
      ∑ i, ((b.repr s i : ℤ) : ZMod n) • Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) := by
  conv_lhs => rw [← b.sum_repr s]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul]

theorem quotSpanNat_linearIndependent {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    LinearIndependent (ZMod n) (fun i => Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set c : ι → ℤ := fun i => ((g i).val : ℤ) with hc
  have hcg : ∀ i, ((c i : ℤ) : ZMod n) = g i := fun i => by simp [c]
  have h0 : Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (∑ i, c i • b i) = 0 := by
    rw [quotSpanNat_mk_eq_sum b n, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [b.repr_sum_self c, hcg]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  have hrep := congrArg (fun y => b.repr y i) ha
  simp only [b.repr_sum_self c] at hrep
  have : a * ((n : ℕ) : S) = ((n : ℤ)) • a := by
    rw [zsmul_eq_mul, mul_comm]; simp
  rw [this, map_zsmul] at hrep
  rw [← hcg i, ← hrep]
  simp

noncomputable def zmodRingHomOfCastEqZero {R : Type} [CommRing R] (n : ℕ) (h : (n : R) = 0) :
    ZMod n →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(n : ℤ)}) (Int.castRingHom R) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      simp [h])).comp (Int.quotientSpanNatEquivZMod n).symm.toRingHom

noncomputable def quotSpanNatBasis {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] :
    Module.Basis ι (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) :=
  Module.Basis.mk (quotSpanNat_linearIndependent b n) (by
    rintro y -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotSpanNat_mk_eq_sum b n s]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem quotSpanNatBasis_apply {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (i : ι) : quotSpanNatBasis b n i = Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) (b i) :=
  Module.Basis.mk_apply _ _ _

theorem quotSpanNatBasis_repr {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ S) (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})]
    (s : S) (i : ι) : (quotSpanNatBasis b n).repr (Ideal.Quotient.mk (Ideal.span {((n : ℕ) : S)}) s) i =
      ((b.repr s i : ℤ) : ZMod n) := by
  have h := quotSpanNat_mk_eq_sum b n s
  simp_rw [← quotSpanNatBasis_apply b n] at h
  rw [h, (quotSpanNatBasis b n).repr_sum_self]

theorem intCast_trace_eq_trace_quotSpanNat {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (n : ℕ) [NeZero n] [Algebra (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)})] (x : S) :
    ((Algebra.trace ℤ S x : ℤ) : ZMod n) =
      Algebra.trace (ZMod n) (S ⧸ Ideal.span {((n : ℕ) : S)}) (Ideal.Quotient.mk _ x) := by
  let b := Module.Free.chooseBasis ℤ S
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace (quotSpanNatBasis b n)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Int.cast_sum, quotSpanNatBasis_apply, ← map_mul,
    quotSpanNatBasis_repr]

theorem isLocalRing_zmod_primePow (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) : IsLocalRing (ZMod (l ^ b)) := by
  have : Fact (1 < l ^ b) := ⟨Nat.one_lt_pow hb (Fact.out : l.Prime).one_lt⟩
  exact IsLocalRing.of_surjective' (PadicInt.toZModPow (p := l) b) (ZMod.ringHom_surjective _)

theorem free_finite_fst_of_prod (l b : ℕ) [Fact l.Prime] (M N : Type) [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod (l ^ b)) M] [Module (ZMod (l ^ b)) N] [Module.Free (ZMod (l ^ b)) (M × N)]
    [Module.Finite (ZMod (l ^ b)) (M × N)] :
    Module.Free (ZMod (l ^ b)) M ∧ Module.Finite (ZMod (l ^ b)) M := by
  rcases eq_or_ne b 0 with rfl | hb
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton M := by
      refine ⟨fun x y => ?_⟩
      rw [← one_smul (ZMod (l ^ 0)) x, ← one_smul (ZMod (l ^ 0)) y, Subsingleton.elim (1 : ZMod (l ^ 0)) 0,
        zero_smul, zero_smul]
    exact ⟨inferInstance, inferInstance⟩
  haveI := isLocalRing_zmod_primePow l b hb
  haveI : Module.Projective (ZMod (l ^ b)) M :=
    Module.Projective.of_split (LinearMap.inl _ M N) (LinearMap.fst _ M N) (by ext; simp)
  haveI : Module.Finite (ZMod (l ^ b)) M :=
    Module.Finite.of_surjective (LinearMap.fst _ M N) LinearMap.fst_surjective
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

theorem intCast_trace_eq_trace_quotient_of_mem (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime]
    (I Q : Ideal (𝓞 L)) (hsup : I ⊔ Q = ⊤) (hmul : I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)})
    [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L) (hx : x ∈ Q) :
    ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) =
      Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hnIQ : ((l ^ b : ℕ) : 𝓞 L) ∈ I * Q := by rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hnQ : ((l ^ b : ℕ) : 𝓞 L) ∈ Q := (Ideal.mul_le_inf.trans inf_le_right) hnIQ
  letI instJ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _)).toAlgebra
  letI instQ : Algebra (ZMod (l ^ b)) (𝓞 L ⧸ Q) :=
    (zmodRingHomOfCastEqZero (l ^ b) (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hnQ)).toAlgebra
  have hcop : IsCoprime I Q := Ideal.isCoprime_iff_sup_eq.mpr hsup
  let e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃+* (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    (Ideal.quotEquivOfEq hmul.symm).trans (Ideal.quotientMulEquivQuotientProd I Q hcop)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) y) = (Ideal.Quotient.mk I y, Ideal.Quotient.mk Q y) := by
    intro y
    refine Prod.ext ?_ ?_ <;>
      simp [e, Ideal.quotientMulEquivQuotientProd_fst, Ideal.quotientMulEquivQuotientProd_snd,
        Ideal.Quotient.factor_mk]
  let eA : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) ≃ₐ[ZMod (l ^ b)] (𝓞 L ⧸ I) × (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e) (fun r => congrArg (fun f => f r)
      (Subsingleton.elim ((e : (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) →+* _).comp (algebraMap (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)})))
        (algebraMap (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)))))
  haveI hfreeJ : Module.Free (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Free.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI hfinJ : Module.Finite (ZMod (l ^ b)) (𝓞 L ⧸ Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) :=
    Module.Finite.of_basis (quotSpanNatBasis (Module.Free.chooseBasis ℤ (𝓞 L)) (l ^ b))
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Free.of_equiv eA.toLinearEquiv
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ I) × (𝓞 L ⧸ Q)) := Module.Finite.equiv eA.toLinearEquiv
  obtain ⟨hfI, hfinI⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ I) (𝓞 L ⧸ Q)
  haveI : Module.Free (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Free.of_equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  haveI : Module.Finite (ZMod (l ^ b)) ((𝓞 L ⧸ Q) × (𝓞 L ⧸ I)) :=
    Module.Finite.equiv (LinearEquiv.prodComm (ZMod (l ^ b)) (𝓞 L ⧸ I) (𝓞 L ⧸ Q))
  obtain ⟨hfQ, hfinQ⟩ := free_finite_fst_of_prod l b (𝓞 L ⧸ Q) (𝓞 L ⧸ I)
  rw [intCast_trace_eq_trace_quotSpanNat (l ^ b) x, ← Algebra.trace_eq_of_algEquiv eA]
  have : eA (Ideal.Quotient.mk (Ideal.span {((l ^ b : ℕ) : 𝓞 L)}) x) = (Ideal.Quotient.mk I x, 0) := by
    show e _ = _
    rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  rw [this, Algebra.trace_prod_apply, map_zero, add_zero]

end GlobalTheory
