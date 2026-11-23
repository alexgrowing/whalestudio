import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl

namespace GlobalTheory.HWL.TensorWitt

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W]

private theorem crd_tmul_lemma (i : I) (o : O) (v : W) :
    crd b i (o ⊗ₜ[Z] v) = b.coord i o • v := by
  simp only [crd, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lsmul_apply]

private theorem crd_mul_lemma_2 (i : I) (c : W) (y : O ⊗[Z] W) :
    crd b i ((1 : O) ⊗ₜ[Z] c * y) = c * crd b i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma]
    exact (mul_smul_comm _ _ _).symm
  | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]

private theorem sum_basis_tmul_crd_eq (y : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    simp_rw [crd_tmul_lemma, Module.Basis.coord_apply, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add y z hy hz =>
    simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 (j : I) (v : I → W) : crd b j (∑ i, b i ⊗ₜ[Z] v i) = v j := by
  classical
  simp [map_sum, crd_tmul_lemma, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mem_pow_iff (w : W) (n : ℕ) (x : O ⊗[Z] W) :
    x ∈ Ideal.span {((1 : O) ⊗ₜ[Z] w) ^ n} ↔ ∀ i, crd b i x ∈ Ideal.span {w ^ n} := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Ideal.mem_span_singleton]
  simp_rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨crd b i y, crd_mul_lemma_2 b i _ y⟩
  · intro h
    choose c hc using h
    refine ⟨∑ i, b i ⊗ₜ[Z] c i, ?_⟩
    conv_lhs => rw [← sum_basis_tmul_crd_eq b x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

include b in

theorem complete_tensor (w : W) [h : IsAdicComplete (Ideal.span {w}) W] :
    IsAdicComplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
  have key : ∀ (n : ℕ) (x : O ⊗[Z] W),
      x ∈ (Ideal.span {(1 : O) ⊗ₜ[Z] w} ^ n • ⊤ : Submodule (O ⊗[Z] W) (O ⊗[Z] W)) ↔
        ∀ i, crd b i x ∈ (Ideal.span {w} ^ n • ⊤ : Submodule W W) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact mem_pow_iff b w n x
  have H1 : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun x hx => ?_⟩
    have hi : ∀ i, crd b i x = 0 := fun i =>
      IsHausdorff.haus h.toIsHausdorff _ fun n => by
        rw [SModEq.sub_mem, sub_zero]
        exact (key n x).1 (by simpa [SModEq.sub_mem] using hx n) i
    rw [← sum_basis_tmul_crd_eq b x]
    simp [hi]
  have H2 : IsPrecomplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun f hf => ?_⟩
    have hfi : ∀ i, ∃ L : W, ∀ n,
        crd b i (f n) ≡ L [SMOD (Ideal.span {w} ^ n • ⊤ : Submodule W W)] := fun i =>
      IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (key m _).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hfi
    refine ⟨∑ i, b i ⊗ₜ[Z] L i, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    rw [map_sub, crd_sum_lemma_4]
    exact SModEq.sub_mem.1 (hL i n)
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

end Coord

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) := by
  unfold inclW
  exact WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem tiltWitt_eq_zero_of_prime_mul_eq_zero (x : WCb l) (h : ((l : ℕ) : WCb l) * x = 0) : x = 0 := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  ext n
  have h1 := WittVector.mul_charP_coeff_succ (p := l) x n
  rw [mul_comm, h, WittVector.zero_coeff] at h1
  rw [WittVector.zero_coeff]
  exact (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero).1 h1.symm

theorem ainf_saturated_in_tiltWitt_prime (a : Loc.Ainf l) (w : WCb l) (h : inclW l a = ((l : ℕ) : WCb l) * w) :
    ∃ a', inclW l a' = w := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  refine ⟨WittVector.mk l fun n => (frobeniusEquiv (OCb l) l).symm (a.coeff (n + 1)), ?_⟩
  ext n
  have h1 := congrArg (fun z : WCb l => z.coeff (n + 1)) h
  simp only [inclW, WittVector.map_coeff] at h1
  rw [mul_comm, WittVector.mul_charP_coeff_succ] at h1
  apply frobenius_inj (Cb l) l
  simp only [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  rw [← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, h1, frobenius_def]

theorem not_isUnit_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    ¬ IsUnit (WittVector.teichmuller l e - 1 : Loc.Ainf l) := by
  intro hu
  apply he
  have h1 := hu.map (WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l)
  rwa [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h1

private theorem crd_tensorProduct_map_eq {Z O I W W' : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']
    (f : W →ₐ[Z] W') (i : I) (y : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f y) = f (crd b i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, crd_tmul_lemma, crd_tmul_lemma, map_smul]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

private theorem tensor_eq_of_crd_eq {Z O I W : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] {y y' : O ⊗[Z] W}
    (h : ∀ i, crd b i y = crd b i y') : y = y' := by
  rw [← sum_basis_tmul_crd_eq b y, ← sum_basis_tmul_crd_eq b y']
  simp_rw [h]

private theorem exists_basis_padicInt_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    ∃ (I : Type) (_ : Fintype I), Nonempty (Module.Basis I ℤ_[l] ↥(OL LL)) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := .of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    refine h.imp (fun h => ?_) id
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h
  haveI : Module.Free ℤ_[l] ↥(OL LL) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  exact ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ_[l] ↥(OL LL)⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (Ideal.span {((l : ℕ) : RW LL)}) (RW LL) ∧
    (∀ x : RW LL, ((l : ℕ) : RW LL) * x = 0 → x = 0) ∧ Function.Injective (inclR LL) ∧
    (∀ (y : RA LL) (x : RW LL), inclR LL y = ((l : ℕ) : RW LL) * x → ∃ y', inclR LL y' = x) ∧
    ∀ e : OCb l, ¬ IsUnit (e - 1) →
      IsAdicComplete (Ideal.span {(1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)})
        (RA LL) := by
  intro l _ LL
  obtain ⟨I, _, ⟨b⟩⟩ := exists_basis_padicInt_OL l LL
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hl' : ∀ i (x : RW LL), crd b i (((l : ℕ) : RW LL) * x) = ((l : ℕ) : WCb l) * crd b i x := by
    intro i x
    rw [hl]
    exact crd_mul_lemma_2 b i _ x
  have hinc : ∀ (y : RA LL) i, crd b i (inclR LL y) = inclW l (crd b i y) := fun y i =>
    crd_tensorProduct_map_eq b (inclWA l) i y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    haveI : IsAdicComplete (Ideal.span {((l : ℕ) : WCb l)}) (WCb l) :=
      (GlobalTheory.Per.AinfComplete.witt_complete (p := l) (R := Cb l) ((l : ℕ) : WCb l)
        (fun c => ⟨c, fun n => by simp⟩)
        (fun x hx => by simpa using hx 1)).2
    exact complete_tensor b _
  · intro x hx
    refine tensor_eq_of_crd_eq b fun i => ?_
    rw [map_zero]
    exact tiltWitt_eq_zero_of_prime_mul_eq_zero _ (by rw [← hl', hx, map_zero])
  · intro y y' h
    exact tensor_eq_of_crd_eq b fun i => inclW_injective (by rw [← hinc, ← hinc, h])
  · intro y x hyx
    have hi : ∀ i, ∃ a' : Loc.Ainf l, inclW l a' = crd b i x := fun i =>
      ainf_saturated_in_tiltWitt_prime (crd b i y) (crd b i x)
        ((hinc y i).symm.trans ((congrArg (crd b i) hyx).trans (hl' i x)))
    choose a' ha' using hi
    refine ⟨∑ i, b i ⊗ₜ[ℤ_[l]] a' i, tensor_eq_of_crd_eq b fun i => ?_⟩
    exact (hinc _ i).trans ((congrArg (inclW l) (crd_sum_lemma_4 b i a')).trans (ha' i))
  · intro e he
    haveI : IsAdicComplete (Ideal.span {(WittVector.teichmuller l e - 1 : Ainf l)}) (Ainf l) :=
      (GlobalTheory.Per.AinfComplete.main l _ (not_isUnit_teich e he)).2
    exact complete_tensor b _

end GlobalTheory.HWL.TensorWitt
