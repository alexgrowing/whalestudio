import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

namespace UpperTheory.V.Pa.BC

section swap
variable (K A σ : Type) [CommRing K] [CommRing A] [Algebra K A]

private def swF (f : PowerSeries (MvPowerSeries σ A)) : MvPowerSeries σ (PowerSeries A) :=
  fun n => PowerSeries.mk fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f)

private theorem coeff_swF (f : PowerSeries (MvPowerSeries σ A)) (n : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.coeff n (swF A σ f)) = MvPowerSeries.coeff n (PowerSeries.coeff k f) :=
  PowerSeries.coeff_mk k (fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f))

private def sw : PowerSeries (MvPowerSeries σ A) →ₐ[K] MvPowerSeries σ (PowerSeries A) where
  toFun := swF A σ
  map_one' := by
    classical
    ext n k
    rw [coeff_swF]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_one, MvPowerSeries.coeff_one, hn, hk]
  map_mul' f g := by
    classical
    ext n k
    simp only [coeff_swF, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    ext n k
    simp [coeff_swF]
  map_add' f g := by
    ext n k
    simp [coeff_swF]
  commutes' r := by
    classical
    ext n k
    rw [coeff_swF, PowerSeries.algebraMap_apply, PowerSeries.coeff_C, MvPowerSeries.algebraMap_apply,
      MvPowerSeries.algebraMap_apply (A := PowerSeries A), PowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_C, MvPowerSeries.coeff_C, hn, hk]

private theorem sw_bij : Function.Bijective (sw K A σ) := by
  constructor
  · intro f g h
    ext k n
    have := congrArg (fun x => PowerSeries.coeff k (MvPowerSeries.coeff n x)) h
    simpa only [sw, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_swF] using this
  · intro g
    refine ⟨PowerSeries.mk fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A), ?_⟩
    ext n k
    refine (coeff_swF A σ (PowerSeries.mk fun k =>
      (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)) n k).trans ?_
    exact congrArg (MvPowerSeries.coeff n) (PowerSeries.coeff_mk (R := MvPowerSeries σ A) k
      (fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)))

end swap

section tens
variable (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type)

private def ph : O' ⊗[O] MvPowerSeries σ R →ₐ[O'] MvPowerSeries σ (O' ⊗[O] R) :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _)
    (MvPowerSeries.mapAlgHom (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)) (fun _ _ => Commute.all _ _)

private def cf (n : σ →₀ ℕ) : O' ⊗[O] MvPowerSeries σ R →ₗ[O] O' ⊗[O] R :=
  LinearMap.lTensor O' ((MvPowerSeries.coeff n : MvPowerSeries σ R →ₗ[R] R).restrictScalars O)

private theorem cf_tmul (n : σ →₀ ℕ) (o : O') (f : MvPowerSeries σ R) :
    cf O O' R σ n (o ⊗ₜ f) = o ⊗ₜ MvPowerSeries.coeff n f := rfl

private theorem coeff_ph (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) :
    MvPowerSeries.coeff n (ph O O' R σ x) = cf O O' R σ n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul o f =>
    rw [cf_tmul]
    simp [ph, Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul, MvPowerSeries.mapAlgHom]

private theorem ph_bij [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (ph O O' R σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have key : ∀ (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) i,
      TensorProduct.equivFinsuppOfBasisLeft b (cf O O' R σ n x) i =
        MvPowerSeries.coeff n (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
    intro n x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul o f =>
      rw [cf_tmul]
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rfl
  constructor
  · intro x y h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i n
    rw [← key, ← key, ← coeff_ph, ← coeff_ph, h]
  · intro g
    refine ⟨(TensorProduct.equivFinsuppOfBasisLeft b).symm (Finsupp.equivFunOnFinite.symm fun i =>
      (fun n => TensorProduct.equivFinsuppOfBasisLeft b (MvPowerSeries.coeff n g) i : MvPowerSeries σ R)), ?_⟩
    ext n
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    rw [coeff_ph, key, LinearEquiv.apply_symm_apply]
    rfl

private def tau0 : Til O O' (MvPowerSeries σ R) →ₐ[O'] MvPowerSeries σ (Til O O' R) :=
  (sw O' (O' ⊗[O] R) σ).comp (PowerSeries.mapAlgHom (ph O O' R σ))

private theorem coeff_power_series_restriction (a : Til O O' (MvPowerSeries σ R)) (n : σ →₀ ℕ) (k : ℕ) :
    Til.coeff O O' R k (MvPowerSeries.coeff n (tau0 O O' R σ a)) = cf O O' R σ n (Til.coeff O O' _ k a) := by
  rw [← coeff_ph]
  exact coeff_swF (O' ⊗[O] R) σ (PowerSeries.mapAlgHom (ph O O' R σ) a) n k

private theorem til_ext {a b : Til O O' R} (h : ∀ k, Til.coeff O O' R k a = Til.coeff O O' R k b) : a = b :=
  PowerSeries.ext h

private theorem power_series_restriction_bijective [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (tau0 O O' R σ) := by
  refine (sw_bij O' (O' ⊗[O] R) σ).comp (f := PowerSeries.map (ph O O' R σ).toRingHom) ⟨?_, ?_⟩
  · exact PowerSeries.map_injective _ (ph_bij O O' R σ).1
  · exact PowerSeries.map_surjective _ (ph_bij O O' R σ).2

private theorem coeff_ι (a : R) (k : ℕ) :
    Til.coeff O O' R k (Til.ι O O' R a) = if k = 0 then (1 : O') ⊗ₜ[O] a else 0 :=
  PowerSeries.coeff_C _ _

private theorem coeff_alt (k : ℕ) :
    Til.coeff O O' R k (Til.s O O' R) = if k = 1 then 1 else 0 :=
  PowerSeries.coeff_X _

private theorem coeff_zero' (k : ℕ) : Til.coeff O O' R k 0 = 0 :=
  map_zero (PowerSeries.coeff k : PowerSeries (O' ⊗[O] R) →ₗ[O' ⊗[O] R] _)

private theorem coeff_map' {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (a : Til O O' R) (k : ℕ) :
    Til.coeff O O' R' k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' R k a) := rfl

end tens

end UpperTheory.V.Pa.BC

open UpperTheory.V.Pa.BC in
theorem UpperTheory.V.Pa.BC.til_mvps :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type) [Finite σ], ∃ τ : Til O O' (MvPowerSeries σ R) ≃ₐ[O'] MvPowerSeries σ (Til O O' R), (∀ a, τ (Til.ι O O' _ a) = MvPowerSeries.map (Til.ι O O' R) a) ∧ τ (Til.s O O' _) = MvPowerSeries.C (Til.s O O' R) ∧ (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) a) = MvPowerSeries.C a) ∧ ∀ (c : MvPowerSeries σ R →ₐ[O] R), (∀ z, c z = MvPowerSeries.constantCoeff z) → ∀ a, MvPowerSeries.constantCoeff (τ a) = Til.map O' c a := by
  intro O O' _ _ _ _ _ R _ _ σ _
  classical
  refine ⟨AlgEquiv.ofBijective (tau0 O O' R σ) (power_series_restriction_bijective O O' R σ), ?_, ?_, ?_, ?_⟩
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_map, coeff_ι, coeff_ι]
    split_ifs
    · rfl
    · exact map_zero _
  · refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_alt]
    by_cases hn : n = 0
    · rw [if_pos hn, coeff_alt]
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, hn, MvPowerSeries.coeff_zero_one]; rfl
      · exact map_zero _
    · rw [if_neg hn, coeff_zero']
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, MvPowerSeries.coeff_one, if_neg hn, TensorProduct.tmul_zero]
      · exact map_zero _
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_map']
    have h : ∀ x : O' ⊗[O] R, cf O O' R σ n (Algebra.TensorProduct.map (AlgHom.id O' O')
        (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) x) = if n = 0 then x else 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]; split_ifs <;> simp
      | tmul o r =>
        rw [Algebra.TensorProduct.map_tmul, cf_tmul]
        split_ifs with hn <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, hn]
    rw [h]
    split_ifs
    · rfl
    · exact (coeff_zero' O O' R k).symm
  · intro c hc a
    refine til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_power_series_restriction, coeff_map']
    generalize Til.coeff O O' _ k a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul o r =>
      rw [Algebra.TensorProduct.map_tmul, cf_tmul, hc]
      rfl
