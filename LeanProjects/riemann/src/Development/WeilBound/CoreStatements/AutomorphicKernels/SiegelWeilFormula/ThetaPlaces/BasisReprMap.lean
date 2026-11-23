import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

section Repr

variable {k : Type} [Field k] {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra k R] [Algebra k S]
  [Algebra k B]

theorem basis_repr_map' {J : Type} (b : Module.Basis J k B) (ρ : R →ₐ[k] S) (x : R ⊗[k] B) (i : J) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map ρ (AlgHom.id k B) x) i =
      ρ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

end Repr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiV (v : HeightOneSpectrum (𝓞 F)) : HeckeCharacterZeroLocus.SiegelWeilU.AF F →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v :=
  (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)

def mapV (v : HeightOneSpectrum (𝓞 F)) :
    HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (phiV v) (AlgHom.id F E)

theorem mapV_eq (v : HeightOneSpectrum (𝓞 F)) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    mapV v x = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def IntV (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F

theorem ev_int_adele (a : HeckeCharacterZeroLocus.SiegelWeilU.AF F) :
    ∀ᶠ v in cofinite, phiV v a ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [a.2.2] with v hv
  exact hv

theorem ev_int_F (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) f ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [ev_int_adele (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.AF F) f)] with v hv
  rwa [AlgHom.commutes] at hv

theorem intV_sum (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (z : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, IntV bs v (z i)) : IntV bs v (∑ i ∈ s, z i) := by
  intro k
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => h i hi k

theorem ev_mul_int (bs : Module.Basis (Fin 2) F E) (c : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v in cofinite, ∀ z, IntV bs v z → IntV bs v (mapV v c * z) := by
  set bA := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) bs
  have h1 : ∀ᶠ v in cofinite, ∀ k, phiV v (bA.repr c k) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int_adele _
  have h2 : ∀ᶠ v in cofinite, ∀ k j l, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (bs.repr (bs k * bs j) l) ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun l => ev_int_F _
  filter_upwards [h1, h2] with v hv1 hv2
  intro z hz l
  set bV := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  have hc : mapV v c = ∑ k, phiV v (bA.repr c k) • bV k := by
    conv_lhs => rw [← bV.sum_repr (mapV v c)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mapV, basis_repr_map']
  have hzz : z = ∑ j, bV.repr z j • bV j := (bV.sum_repr z).symm
  have hprod : bV.repr (mapV v c * z) l =
      ∑ k, ∑ j, (phiV v (bA.repr c k) * bV.repr z j) * algebraMap F _ (bs.repr (bs k * bs j) l) := by
    rw [hc]
    conv_lhs => rw [hzz]
    rw [Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, bV, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, one_smul]
  rw [hprod]
  exact sum_mem fun k _ => sum_mem fun j _ => mul_mem (mul_mem (hv1 k) (hz j)) (hv2 k j l)

def IntM (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : Prop := ∀ i j, IntV bs v (M i j)

theorem ev_matmul_int (bs : Module.Basis (Fin 2) F E) {q : ℕ} (A : Matrix (Fin q) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v in cofinite, ∀ (p : ℕ) (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)),
      IntM bs v M → IntM bs v (M * A.map (mapV v)) := by
  have h : ∀ᶠ v in cofinite, ∀ i j, ∀ z, IntV bs v z → IntV bs v (mapV v (A i j) * z) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_mul_int bs (A i j)
  filter_upwards [h] with v hv
  intro p M hM i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine intV_sum bs v _ _ fun l _ => ?_
  rw [mul_comm]
  exact hv l j _ (hM i l)

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

end
