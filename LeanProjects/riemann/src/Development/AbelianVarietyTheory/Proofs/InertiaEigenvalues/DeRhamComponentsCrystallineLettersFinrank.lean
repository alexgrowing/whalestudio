import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDimStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.Components

theorem card_le_of_idem_indep {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section Bound

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K]
    [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]

open GlobalTheory.DRFil in

theorem finrank_DdRE_le (hF : IsField F) (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] : finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem_indep (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

end Bound

theorem exists_baseChange {G : Type} [Group G] (Qp LL LL' : Type) [Field Qp] [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module LL' V') (_ : Module LL V') (_ : Module Qp V')
      (_ : IsScalarTower Qp LL' V') (_ : IsScalarTower LL LL' V') (_ : FiniteDimensional LL' V')
      (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'),
      IsBaseChange LL' j ∧ ∀ g x, j (ρ g x) = ρ' g (j x) :=
  ⟨LL' ⊗[LL] V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (Module.End.baseChangeHom LL LL' V).toMonoidHom.comp ρ, TensorProduct.mk LL LL' V 1,
    TensorProduct.isBaseChange LL V LL', fun _ _ => rfl⟩

theorem components_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ≤ finrank ↥LL.1 V ∧ (IsDR (P.PD K) ρ → finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V)) ∧ ∀ τ, IsCrys (P.PD K) ρ → finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := K.2
  obtain ⟨LL', ⟨f⟩, hK, hK0⟩ := GlobalTheory.exists_finExt_embedding_splitting l K ↥LL.1
  haveI := LL'.2
  letI : Algebra ↥LL.1 ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ↥LL.1 ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  obtain ⟨V', _, _, _, _, _, _, _, ρ', j, hj, hρj⟩ := exists_baseChange ℚ_[l] ↥LL.1 ↥LL'.1 ρ
  obtain ⟨hV, -, ⟨hc, -⟩, ⟨hd, -⟩, -, hl, he⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) ↥LL.1 ↥LL'.1 V V' ρ ρ' j hj hρj
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim l P AI T K LL' V' ρ'
  refine ⟨fun τ => ?_, fun τ hρ => ?_⟩
  · haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
    haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
    refine ⟨this, finrank_DdRE_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ τ, fun hρ => ?_⟩
    rw [← (he τ).1, ← hV]
    refine h2 hK ?_ _
    unfold IsDR at hρ ⊢
    rw [hd, hV, hρ]
  · rw [← hl τ, ← hV]
    refine h1 hK0 ?_ _
    unfold IsCrys at hρ ⊢
    rw [hc, hV, hρ]

end GlobalTheory.Per.Components
