import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatFibreInjective

open TensorProduct

theorem one_tmul_ne_zero_of_domain {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by
  intro h1
  letI : Algebra (FractionRing A) k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower A (FractionRing A) k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinj a).symm)
  haveI : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  haveI : Module.Free (FractionRing A) k := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing A) k := Module.Flat.of_free
  haveI : Module.Flat A k := Module.Flat.trans _ (FractionRing A) _
  have hi : Function.Injective (LinearMap.toSpanSingleton A P y) := by
    rw [injective_iff_map_eq_zero]
    exact hy
  have h2 : (1 : k) ⊗ₜ[A] (1 : A) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) _ hi
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, map_zero, h1]
  have h3 := congrArg (TensorProduct.rid A k) h2
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h3
  exact one_ne_zero h3

theorem one_tmul_ne_zero {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by
  intro h
  have hker : p = RingHom.ker (algebraMap R₀ k) := by
    ext a; simp [RingHom.mem_ker, hk]
  haveI : p.IsPrime := hker ▸ RingHom.ker_isPrime _
  letI : Module (R₀ ⧸ p) P := hP.module
  haveI : IsScalarTower R₀ (R₀ ⧸ p) P := hP.isScalarTower
  letI : Algebra (R₀ ⧸ p) k :=
    (Ideal.Quotient.lift p (algebraMap R₀ k) (fun a ha => (hk a).2 ha)).toAlgebra
  haveI : IsScalarTower R₀ (R₀ ⧸ p) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (R₀ ⧸ p) k) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hk a).1 ha)
  refine one_tmul_ne_zero_of_domain (A := R₀ ⧸ p) hinj y ?_ ?_
  · intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hy a ha)
  · have := congrArg (TensorProduct.mapOfCompatibleSMul (R₀ ⧸ p) R₀ R₀ k P) h
    rwa [TensorProduct.mapOfCompatibleSMul_tmul, map_zero] at this

theorem one_tmul_eq_zero {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by
  obtain ⟨g, hg⟩ := (φ.baseChange k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hφ)
  have key : ∀ z : M ⊗[R₀] C₀,
      TensorProduct.leftComm R₀ M k C₀ ((g.restrictScalars R₀).lTensor M
        ((TensorProduct.mk R₀ k C₁ 1).lTensor M (φ.lTensor M z))) = (1 : k) ⊗ₜ[R₀] z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      have := LinearMap.congr_fun hg ((1 : k) ⊗ₜ[R₀] c)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at this
      simp [this]
    | add a b ha hb => simp only [map_add, ha, hb, tmul_add]
  rw [← key, hy]
  simp

theorem exists_of_torsion {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by
  classical
  obtain ⟨s, rfl⟩ := hp
  let g : N →ₗ[R₀] (s → N) := LinearMap.pi fun a => (a : R₀) • LinearMap.id
  have hex : Function.Exact (Submodule.torsionBySet R₀ N (Ideal.span (s : Set R₀))).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← Submodule.torsionBySet_eq_torsionBySet_span]
    ext n
    simp [g, funext_iff, LinearMap.mem_ker]
  have h := Module.Flat.rTensor_exact C hex x
  refine h.1 ?_
  apply (TensorProduct.piLeft R₀ C (fun _ : s => N)).injective
  have key : ∀ z : N ⊗[R₀] C, ∀ a : s,
      TensorProduct.piLeft R₀ C (fun _ : s => N) (g.rTensor C z) a = (a : R₀) • z := by
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n c => simp [g, smul_tmul']
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, smul_add]
  funext a
  rw [key, hx _ (Ideal.subset_span a.2)]
  simp

theorem injective_baseChange :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by
  intro R₀ R C₀ C₁ _ _ _ _ _ _ _ _ _ _ φ H
  change Function.Injective (φ.lTensor R)
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  haveI : Nontrivial (LinearMap.ker (φ.lTensor R)) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R₀ (LinearMap.ker (φ.lTensor R))
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, ⟨x, hx0⟩, hx⟩ := hp
  have hann : ∀ a : R₀, a • x = 0 ↔ a ∈ p := by
    intro a
    rw [hx]
    simp [Submodule.mem_colon_singleton]
  let M := Submodule.torsionBySet R₀ R p
  obtain ⟨y, rfl⟩ : ∃ y, M.subtype.rTensor C₀ y = x :=
    exists_of_torsion p (IsNoetherian.noetherian p) x (fun a ha => (hann a).2 ha)
  have hy0 : φ.lTensor M y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype M.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor]
    exact hx0
  have hkill : ∀ a : R₀, (∀ m : M, a • m = 0) → ∀ z : M ⊗[R₀] C₀, a • z = 0 := by
    intro a ha z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rw [smul_tmul', ha, zero_tmul]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  have hy : ∀ a : R₀, a • y = 0 → a ∈ p := by
    intro a ha
    rw [← hann, ← map_smul, ha, map_zero]
  have hcm : (p.map (algebraMap R₀ R)).comap (algebraMap R₀ R) = p := by
    refine le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    refine hy a (hkill a (fun m => ?_) y)
    have hle : p.map (algebraMap R₀ R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R R m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      have := (Submodule.mem_torsionBySet_iff _ _).1 m.2 ⟨b, hb⟩
      simpa [Algebra.smul_def] using this
    have := hle ha
    apply Subtype.ext
    simpa [Algebra.smul_def] using this
  obtain ⟨q, hq, hqp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).1 hcm
  refine one_tmul_ne_zero (k := q.ResidueField) p ?_ ?_ y hy
    (one_tmul_eq_zero φ (H q.ResidueField) y hy0)
  · intro a
    rw [IsScalarTower.algebraMap_apply R₀ R q.ResidueField, Ideal.algebraMap_residueField_eq_zero,
      ← hqp]
    rfl
  · intro z a
    refine hkill a (fun m => Subtype.ext ?_) z
    exact (Submodule.mem_torsionBySet_iff _ _).1 m.2 a

end GlobalTheory.FlatFibreInjective
