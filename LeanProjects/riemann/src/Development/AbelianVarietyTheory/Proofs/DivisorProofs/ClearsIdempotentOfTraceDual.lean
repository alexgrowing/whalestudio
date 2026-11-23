import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DualCrit

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    algebraMap ℚ K (Algebra.trace ℚ E x) = ∑ σ : E →+* K, σ x := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  apply ι.injective
  rw [map_sum]
  have hq : ι.comp (algebraMap ℚ K) = algebraMap ℚ (AlgebraicClosure K) := RingHom.ext_rat _ _
  rw [← RingHom.comp_apply, hq, trace_eq_sum_embeddings (AlgebraicClosure K)]
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun σ => (ι.comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ σ' h
    ext y
    apply ι.injective
    exact congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcard, AlgHom.card]
  exact (Fintype.sum_bijective f hbij (fun σ => ι (σ x)) (fun τ => τ x) (fun σ => rfl)).symm

theorem sum_basis_mul_dual {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (σ σ' : E →+* K) :
    ∑ j, σ' (b j) * σ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b j) =
      if σ' = σ then 1 else 0 := by
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  let A : Matrix ι (E →+* K) K := fun j τ => τ (b j)
  let B : Matrix (E →+* K) ι K := fun τ k => τ (bd k)
  have hAB : A * B = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, B]
    rw [show (∑ τ : E →+* K, τ (b j) * τ (bd k)) = ∑ τ : E →+* K, τ (bd k * b j) from
      Finset.sum_congr rfl fun τ _ => by rw [map_mul, mul_comm]]
    rw [← trace_eq_sum_ringHom hcard, ← Algebra.traceForm_apply,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have e : ι ≃ (E →+* K) := Fintype.equivOfCardEq (by rw [hcard, Module.finrank_eq_card_basis b])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have h := congrFun (congrFun hBA σ) σ'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [A, B] at h
  calc _ = ∑ k, σ (bd k) * σ' (b k) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by rw [h]; exact if_congr eq_comm rfl rfl

theorem clearsIdem_top_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  intro E _ _ _ O _ _ _ _ K _ _ _ hcard D hD σ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  haveI : Finite (E →+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* K) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, hcard]
  set b := RingOfIntegers.basis E
  set bQ := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) bQ
  have hint : ∀ j (x : 𝓞 E), ∃ n : ℤ, Algebra.trace ℚ E (bd j * x) = n := by
    intro j x
    refine ⟨b.repr x j, ?_⟩
    have h1 : Algebra.trace ℚ E (bd j * x) = bQ.repr (x : E) j := by
      rw [← Algebra.traceForm_apply]
      conv_lhs => rw [← bQ.sum_repr (x : E)]
      rw [map_sum]
      simp only [bd, map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact (integralBasis_repr_apply E x j).trans (eq_intCast _ _)
  choose z hz using fun j => hD σ (bd j) (hint j)
  have hmem : ∀ j, ((b j : 𝓞 E) : E) ∈ orderC (⊤ : Ideal (OF E)) := fun j =>
    mem_orderC.2 ⟨0, b j, by rw [Ideal.map_top]; exact Submodule.mem_top, by simp⟩
  refine ⟨∑ j, (⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j, fun σ' => ?_⟩
  have hc : ∀ j, coordAt O (⊤ : Ideal (OF E)) σ'
      ((⟨((b j : 𝓞 E) : E), hmem j⟩ : orderC (⊤ : Ideal (OF E))) ⊗ₜ[ℤ] z j) =
        algebraMap O K D * (σ' (bQ j) * σ (bd j)) := by
    intro j
    show σ' ((b j : 𝓞 E) : E) * algebraMap O K (z j) = _
    rw [hz j, integralBasis_apply]
    simp only [b]
    rw [← RingOfIntegers.coe_eq_algebraMap]
    ring
  rw [map_sum, Finset.sum_congr rfl fun j _ => hc j, ← Finset.mul_sum, sum_basis_mul_dual hcard' bQ σ σ']
  split_ifs <;> simp

end GlobalTheory.DualCrit
