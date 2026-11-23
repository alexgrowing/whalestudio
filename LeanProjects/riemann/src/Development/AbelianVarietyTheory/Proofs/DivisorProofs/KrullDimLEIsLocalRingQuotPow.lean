import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.LowBaseChange

theorem krullDimLE_isLocalRing_quot_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 1 0 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

variable {R : Type} [CommRing R]

theorem one_tmul_eq_zero_iff {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R)
    (t : (R ⧸ I) ⊗[R] M) : ∃ x : M, (1 : R ⧸ I) ⊗ₜ[R] x = t :=
  TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective t

theorem projective_coker_of_approx [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by
  haveI : IsNoetherian R B := isNoetherian_of_isNoetherianRing_of_finite R B
  have hinjq : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ m)) := by
    intro m _
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := exists_one_tmul m t
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, one_tmul_eq_zero_iff] at ht
    set N := B ⧸ (m • LinearMap.range f)
    have hq : (m • LinearMap.range f).mkQ (f a) ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R N) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨y, hy, hay⟩ := hyp m n a ht
      have e : (m • LinearMap.range f).mkQ (f a) = (m • LinearMap.range f).mkQ (f y) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hay
      rw [e]
      have hle : m ^ (n + 1) • (⊤ : Submodule R B) ≤
          (m ^ n • (⊤ : Submodule R N)).comap (m • LinearMap.range f).mkQ := by
        refine Submodule.smul_le.2 fun r hr x _ => ?_
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hr) Submodule.mem_top
      exact hle hy
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff _).1 hq
    have h1 : f a - (r : R) • f a ∈ m • LinearMap.range f := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul]
      exact hr.symm
    have hsplit : (⟨f a, LinearMap.mem_range_self f a⟩ : LinearMap.range f) =
        ⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a) (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ +
          (r : R) • ⟨f a, LinearMap.mem_range_self f a⟩ := by
      ext; simp
    rw [hsplit, TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
    have h2 : (1 : R ⧸ m) ⊗ₜ[R] (⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a)
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ : LinearMap.range f) = 0 := by
      rw [one_tmul_eq_zero_iff, Submodule.mem_smul_top_iff]; exact h1
    rw [h2, zero_add, Algebra.smul_def, _root_.mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 r.2, TensorProduct.zero_tmul]
  have hinj : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor m.ResidueField) := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have hL : RingHom.ker (algebraMap R (R ⧸ m)) = m := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have := GlobalTheory.exact_lTensor_iff_residueField m (R ⧸ m) hL
      (0 : PUnit →ₗ[R] LinearMap.range f) (LinearMap.range f).subtype
    rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective,
      LinearMap.exact_zero_iff_injective] at this
    exact this.1 (hinjq m)
  obtain ⟨l, hl⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
    (LinearMap.range f).subtype hinj
  have hex := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
  obtain ⟨s, hs⟩ := hex.2 ⟨l, hl⟩
  exact Module.Projective.of_split s _ hs

end GlobalTheory.AbCoh.LowBaseChange

open GlobalTheory.AbCoh.LowBaseChange in

theorem GlobalTheory.AbCoh.projective_coker_of_liftsAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  intro R _ _ K hK _ hL i hi
  haveI := (hK (i + 1)).1
  haveI := (hK (i + 1)).2
  refine projective_coker_of_approx (K.d i (i + 1)).hom ?_
  intro m _ n a ha
  obtain ⟨h0, h1⟩ := krullDimLE_isLocalRing_quot_pow m n
  haveI := h1
  haveI : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, h0⟩
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hle : m ^ (n + 1) ≤ m := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let α : (R ⧸ m ^ (n + 1)) →ₐ[R] (R ⧸ m) := Ideal.Quotient.factorₐ R hle
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hz : dB K (R ⧸ m) i (i + 1) ((1 : R ⧸ m) ⊗ₜ[R] a) = 0 := by
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
    exact ha
  obtain ⟨y, b, hy, hyb⟩ := hL i hi (R ⧸ m ^ (n + 1)) (R ⧸ m) α hα _ hz
  obtain ⟨y₀, rfl⟩ := exists_one_tmul _ y
  obtain ⟨b₀, rfl⟩ := exists_one_tmul _ b
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hy
  refine ⟨y₀, hy, ?_⟩
  rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← TensorProduct.tmul_add] at hyb
  have hdd : (K.d i (i + 1)).hom ((K.d (i - 1) i).hom b₀) = 0 := by
    have := congrArg (fun g => g.hom b₀) (K.d_comp_d (i - 1) i (i + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have hm : a - (y₀ + (K.d (i - 1) i).hom b₀) ∈ m • (⊤ : Submodule R (K.X i)) := by
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← hyb, sub_self]
  have := Submodule.mem_map_of_mem (f := (K.d i (i + 1)).hom) hm
  rw [Submodule.map_smul'', ← LinearMap.range_eq_map, map_sub, map_add, hdd, add_zero] at this
  exact this
