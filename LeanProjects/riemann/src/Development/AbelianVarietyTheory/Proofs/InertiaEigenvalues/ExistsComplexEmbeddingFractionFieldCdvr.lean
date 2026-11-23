import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_of_mk_le_continuum {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    simpa [Cardinal.mkRat] using this
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hst : #s ≤ #t := by
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    rw [← h1, Cardinal.mk_complex]
    exact (Cardinal.mk_subtype_le _).trans hΩ
  obtain ⟨e⟩ := hst
  have hv : AlgebraicIndependent K (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let f : IntermediateField.adjoin K (Set.range ((↑) : s → Ω)) →ₐ[K] ℂ :=
    (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
  have halg := hs.isAlgebraic_field
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' f
    (fun (x : Ω) => ⟨(Algebra.IsAlgebraic.isAlgebraic
      (R := IntermediateField.adjoin K (Set.range ((↑) : s → Ω))) x).isIntegral, IsAlgClosed.splits _⟩)
  refine ⟨φ.toRingHom, ?_⟩
  ext x
  exact φ.commutes x

theorem exists_embedding_fractionField :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes →
      ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T hT io
  haveI : Finite (ResidueField T.V) := hT
  have hV := mk_le_continuum_of_finite_residueField T.V
  have hF : #T.Fr ≤ 𝔠 := by
    rw [show #T.Fr = #T.V from IsFractionRing.cardinalMk T.V T.Fr]
    exact hV
  exact @exists_embedding_of_mk_le_continuum K T.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
