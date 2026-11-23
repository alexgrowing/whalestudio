import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QNotPthPowInClosureAlgebraicPadicIntStatement

open GlobalTheory.K5 Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.K5.TauGen

theorem not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt

def geoF (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x})

theorem isOpen_setOf_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (x : Ω) (P : Ω → Prop) : IsOpen {σ : Ω ≃ₐ[F] Ω | P (σ x)} := by
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  have hU : IsOpen (((F⟮x⟯).fixingSubgroup : Subgroup (Ω ≃ₐ[F] Ω)) : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hV : IsOpen ((fun τ : Ω ≃ₐ[F] Ω => σ⁻¹ * τ) ⁻¹' ((F⟮x⟯).fixingSubgroup : Set (Ω ≃ₐ[F] Ω))) :=
    hU.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hV.mem_nhds ?_) ?_
  · show σ⁻¹ * σ ∈ (F⟮x⟯).fixingSubgroup
    rw [inv_mul_cancel]; exact one_mem _
  · intro τ hτ
    have h1 := (mem_fixingSubgroup_iff _ _).1 hτ x (mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have : σ⁻¹ (τ x) = x := h1
      calc τ x = σ (σ⁻¹ (τ x)) := by simp
        _ = σ x := by rw [this]
    show P (τ x)
    rw [h2]; exact hσ

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ T : Tower p Ω, ∃ τ ∈ Ggeo p Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  intro p hp hp2 Ω _ _ hΩ T
  haveI := hΩ.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo hΩ
  have hO : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoF p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hA : ∀ x : Ω, IsAlgZp p x → x ∈ geoF p Ω := fun x hx => Subfield.subset_closure (Or.inr hx)
  let F := geoF p Ω
  let φ : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  have hφ : Function.Injective φ := fun a b h => hΩ.inj (congrArg Subtype.val h)
  have hcomp : (algebraMap F Ω).comp φ = algebraMap (O0 p) Ω := by ext a; rfl
  haveI hal : Algebra.IsAlgebraic F Ω := by
    constructor
    intro x
    obtain ⟨P, hP, hx⟩ := hΩ.alg.isAlgebraic x
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, hx]
  haveI : IsAlgClosure F Ω := ⟨inferInstance, hal⟩
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Ω ≃ₐ[F] Ω) := inferInstance
  let q' : F := ⟨algebraMap (O0 p) Ω (qO p), hO _⟩
  have hirr : ∀ n, Irreducible (X ^ (p ^ n) - C q') := fun n =>
    X_pow_sub_C_irreducible_of_prime_pow hp.out hp2 n (fun b hb =>
      not_pow p Ω hΩ (b : Ω) b.2 (by rw [← SubmonoidClass.coe_pow, hb]))
  have hmin : ∀ n (y : Ω), y ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) → minpoly F y = X ^ (p ^ n) - C q' := by
    intro n y hy
    refine (minpoly.eq_of_irreducible_of_monic (hirr n) ?_ (monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero))).symm
    simp only [map_sub, map_pow, aeval_X, aeval_C, hy]
    exact sub_self _
  let S : ℕ → Set (Ω ≃ₐ[F] Ω) := fun n => {σ | σ (T.qq n) = T.ζ n * T.qq n}
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have h1 := hmin n (T.qq n) (Basic.qq_pow T n)
    have h2 := hmin n (T.ζ n * T.qq n) (by rw [mul_pow, (T.prim n).pow_eq_one, one_mul, Basic.qq_pow T n])
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) Ω).1 (h2.trans h1.symm)
    exact ⟨σ, hσ⟩
  have hdec : ∀ n, S (n + 1) ⊆ S n := by
    intro n σ hσ
    show σ (T.qq n) = T.ζ n * T.qq n
    have hσ' : σ (T.qq (n + 1)) = T.ζ (n + 1) * T.qq (n + 1) := hσ
    rw [← T.qpow n, map_pow, hσ', mul_pow, T.ζpow, T.qpow]
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_apply (F := F) (T.qq n) (fun y => ¬ y = T.ζ n * T.qq n)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  let τ : Gal p Ω :=
    { σ.toRingEquiv with
      commutes' := fun a => σ.commutes (⟨algebraMap (O0 p) Ω a, hO a⟩ : F) }
  refine ⟨τ, fun x hx => σ.commutes (⟨x, hA x hx⟩ : F), fun n => hσ n⟩

end GlobalTheory.K5.TauGen
