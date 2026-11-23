import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediateStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLengthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbeddingStatement
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem length_H1fT_modPow_le : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ _ _ _ V _ _ _ _ _ _ ρ _ _ _ L hfin n
  set Z := latticeFiniteCocycles PD L with hZdef
  set B' : Submodule O (G → V) := (B1 ρ).restrictScalars O with hB'
  set a : O := ((PD.p : ℕ) : O) ^ n with ha
  have hBB : latticeCoboundaries L ≤ B' := by
    rintro c ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hZT : ∀ c ∈ Z, ∀ g, c g ∈ L.T := by
    intro c hc g
    exact (Submodule.mem_pi.mp hc.1.2) g (Set.mem_univ g)
  have hZf : ∀ c ∈ Z, c ∈ finiteCocycles PD ρ := fun c hc => hc.2
  have h1 := GlobalTheory.T.length_quotient_smul_sup_le_intermediate O (G → V) Z (latticeCoboundaries L) B' a hBB
  have h2 := GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le L Z hZT

  let ψ0 : ↥Z →ₗ[O] ↥(finiteCocycles PD ρ) :=
    { toFun := fun c => ⟨c.1, hZf c.1 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r c => rfl }
  let ψ : ↥Z →ₗ[O] FiniteCohomology PD ρ :=
    (((B1 ρ).comap (finiteCocycles PD ρ).subtype).mkQ.restrictScalars O).comp ψ0
  have hker : LinearMap.ker ψ = B'.comap Z.subtype := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let f := (B'.comap Z.subtype).liftQ ψ hker.ge
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have h3 := GlobalTheory.T.length_quotient_smul_le_finrank_of_embedding O LL (FiniteCohomology PD ρ) _ f hf a
  have h4 := GlobalTheory.T.length_quotient_span_pow_le_mul_length O ((PD.p : ℕ) : O) n
  have hl : lenOl PD (O := O) = Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) := rfl
  calc _ ≤ _ := h1
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) +
          Module.length O ↥(Representation.invariants (repD L)) := add_le_add h3 h2
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * ((n : ℕ∞) * lenOl PD (O := O)) +
          Module.length O ↥(Representation.invariants (repD L)) := by
        rw [hl]; gcongr
    _ = _ := by ring

end GlobalTheory
