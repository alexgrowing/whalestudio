import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.LetterDim

theorem card_le_of_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
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

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]

open GlobalTheory.DRFil in

theorem component_le [FiniteDimensional Qp K] [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

theorem component_eq [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (hc : Nat.card (K →ₐ[Qp] LL) = finrank Qp K) (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) :
    finrank LL ↥(DdRE PD ρ τ) = finrank LL V := by
  haveI := PD.finK
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le PD hF ρ).1
  haveI : ∀ τ, FiniteDimensional LL ↥(DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  rw [Nat.card_eq_fintype_card] at hc
  have hs := (GlobalTheory.DeRhamSplit.finrank_DdR PD ρ hc 0).1
  unfold IsDR at h
  refine (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (g := fun _ => finrank LL V)
    fun τ _ => component_le PD hF ρ τ).1 ?_ τ (Finset.mem_univ τ)
  rw [← hs, h, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]

omit [FiniteDimensional Qp LL] in

theorem finite_Dcris (ρ : Representation LL G V) (h : IsCrys PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := PD.finK₀
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := finrank_zero_iff.1 h0
    infer_instance
  · exact FiniteDimensional.of_finrank_pos (by
      unfold IsCrys at h
      rw [h]
      exact Nat.mul_pos finrank_pos h0)

omit [FiniteDimensional Qp LL] in
open GlobalTheory.RegularRing in

theorem letter_eq [IsDomain B] (ρ : Representation LL G V)
    (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (h : IsCrys PD ρ) (τ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD ρ τ) = finrank LL V := by
  haveI := PD.finK₀
  haveI := finite_Dcris PD ρ h
  have hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) →
      finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
    intro n
    induction n with
    | zero =>
      intro τ τ' h
      rw [show τ' = τ from AlgHom.ext h]
    | succ n ih =>
      intro τ τ' h
      exact (ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans
        (letter_le PD ρ τ _ fun _ => rfl)
  have heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ) := fun τ' => by
    obtain ⟨n, hn⟩ := exists_pow_sigma PD LL hc τ τ'
    obtain ⟨n', hn'⟩ := exists_pow_sigma PD LL hc τ' τ
    exact le_antisymm (hle n _ _ hn) (hle n' _ _ hn')
  rw [Nat.card_eq_fintype_card] at hc
  have hs : finrank LL ↥(Dcris PD ρ) = ∑ τ', finrank LL ↥(DcrisL PD ρ τ') :=
    GlobalTheory.DeRhamSplit.finrank_eq_sum hc (GlobalTheory.DeRhamSplit.mulHom Qp K₀ B LL V) (Dcris PD ρ)
      fun a x hx => (GlobalTheory.FontCmp.mK PD ρ a ⟨x, hx⟩).2
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs
  unfold IsCrys at h
  exact Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)

end General

theorem tied_letter_component_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  exact ⟨letter_eq (P.PD K) ρ, component_eq (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ⟩

end GlobalTheory.Per.LetterDim
