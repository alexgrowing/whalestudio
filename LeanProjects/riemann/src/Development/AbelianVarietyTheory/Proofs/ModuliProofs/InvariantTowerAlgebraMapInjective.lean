import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsumSmulEqOneOfTame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulMemSpanInvariantsSup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubalgebraEqTopOfForallPrimeSmulMemSup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem mem_smul_ker_of_flat_quotient {B T C : Type} [CommRing B] [AddCommGroup T] [Module B T]
    [AddCommGroup C] [Module B C] [Module.Flat B C] (φ : T →ₗ[B] C) (hφ : Function.Surjective φ)
    (q : Ideal B) (x : LinearMap.ker φ) (hx : (x : T) ∈ q • (⊤ : Submodule B T)) :
    x ∈ q • (⊤ : Submodule B (LinearMap.ker φ)) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hφ (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map φ) (B ⧸ q)
  have h0 : ∀ (M : Type) [AddCommGroup M] [Module B M] (y : M),
      ((1 : B ⧸ q) ⊗ₜ[B] y = 0 ↔ y ∈ q • (⊤ : Submodule B M)) := by
    intro M _ _ y
    rw [← Submodule.Quotient.mk_eq_zero, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
      LinearEquiv.map_eq_zero_iff]
  rw [← h0]
  apply hinj
  rw [LinearMap.lTensor_tmul, map_zero, h0]
  exact hx

theorem ideal_eq_bot_of_forall_prime_smul_mem {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this

theorem isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAB hRC heq hnoeth hfAB hfRC hflat hcard hI
  classical
  haveI := Fintype.ofFinite Γ
  haveI : SMulCommClass A Γ B := SMulCommClass.symm _ _ _
  let φ : B ⊗[A] R →ₐ[B] C := Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom A R C) (fun _ _ => Commute.all _ _)
  have hφ : ∀ (b : B) (r : R), φ (b ⊗ₜ r) = algebraMap B C b * algebraMap R C r := by
    intro b r
    simp [φ, Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    have := span_range_algebraMap_eq_top_of_tame Γ A B R C hAB hRC heq hfRC hcard hI
    have h2 : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← this, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact ⟨1 ⊗ₜ r, by simp [hφ]⟩
    exact LinearMap.range_eq_top.1 h2
  have hR : ∀ (g : Γ) (r : R), g • algebraMap R C r = algebraMap R C r := by
    intro g r
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hequi : ∀ (g : Γ) (x : B ⊗[A] R), φ (g • x) = g • φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b r => rw [TensorProduct.smul_tmul', hφ, hφ, smul_mul', heq, hR]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  have hsl : ∀ (g : Γ) (b : B) (x : B ⊗[A] R), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  have htr : ∀ x : B ⊗[A] R, ∃ r : R, ∑ g : Γ, g • x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c r =>
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • c) (by
        intro k
        rw [Finset.smul_sum]
        simp only [← mul_smul]
        exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => g • c))
      refine ⟨a • r, ?_⟩
      simp only [TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, ← ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp only [smul_add, Finset.sum_add_distrib, hr, hs, TensorProduct.tmul_add]⟩
  have hinv : ∀ x : B ⊗[A] R, φ x = 0 → (∀ g : Γ, g • x = x) → x = 0 := by
    intro x hx hg
    obtain ⟨b, hb⟩ := exists_finsum_smul_eq_one_of_tame Γ B hcard
    rw [finsum_eq_sum_of_fintype] at hb
    obtain ⟨r, hr⟩ := htr (b • x)
    simp only [hsl, hg] at hr
    rw [← Finset.sum_smul, hb, one_smul] at hr
    rw [hr, hφ, map_one, _root_.one_mul, map_eq_zero_iff _ hRC] at hx
    rw [hr, hx, TensorProduct.tmul_zero]
  have hinert : ∀ q : Ideal B, ∀ g ∈ q.inertia Γ, ∀ x : B ⊗[A] R,
      g • x - x ∈ q • (⊤ : Submodule B (B ⊗[A] R)) := by
    intro q g hg x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      have : g • (c ⊗ₜ[A] r) - c ⊗ₜ[A] r = (g • c - c) • ((1 : B) ⊗ₜ[A] r) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul (hg c) Submodule.mem_top
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  let K : Submodule B (B ⊗[A] R) := LinearMap.ker φ.toLinearMap
  have hK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => Iff.rfl
  letI : SMul Γ K := ⟨fun g x => ⟨g • (x : B ⊗[A] R), by
    rw [hK, hequi, (hK _).1 x.2, smul_zero]⟩⟩
  letI : DistribMulAction Γ K :=
    Function.Injective.distribMulAction K.subtype.toAddMonoidHom K.injective_subtype
      (fun _ _ => rfl)
  haveI : IsNoetherianRing (B ⊗[A] R) := by
    haveI : IsNoetherianRing (R ⊗[A] B) := Algebra.FiniteType.isNoetherianRing R _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hker : RingHom.ker φ = ⊥ := by
    refine ideal_eq_bot_of_forall_prime_smul_mem (B := B) _ (IsNoetherian.noetherian _) ?_
    intro q hq x hx
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_invariants_sup Γ B K
      (fun g b y => Subtype.ext (hsl g b y)) q hq (hcard q hq)
      (fun g hg y => mem_smul_ker_of_flat_quotient φ.toLinearMap hsurj q _ (hinert q g hg y))
      ⟨x, hx⟩
    refine ⟨s, hs, ?_⟩
    have hbot : Submodule.span B {y : K | ∀ g : Γ, g • y = y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      exact Subtype.ext (hinv y y.2 fun g => congrArg Subtype.val (hy g))
    rw [hbot, bot_sup_eq, Submodule.mem_smul_top_iff] at hsx
    exact hsx
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩)
    (fun r => (hφ 1 r).trans (by simp))⟩

end GlobalTheory
