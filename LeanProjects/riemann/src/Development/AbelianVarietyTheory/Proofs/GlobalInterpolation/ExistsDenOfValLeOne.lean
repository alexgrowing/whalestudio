import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemNabStdOfDetMulIntegral

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.HAtBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.HAtBasis.isLattice_of_basisAt {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG)
    {B : GL (Fin n) K} (hB : _root_.Formalism.L2.DIV.IsBasisAt w M B) : Submodule.IsLattice K M := by
  refine ⟨hM, ?_⟩
  have hcol : ∀ j, (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈
      Submodule.span K (M : Set (Fin n → K)) := by
    intro j
    have h1 : (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
      rw [hB]
      apply _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M _).1 h1
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have hs' : s = 0 := by exact_mod_cast h0
      rw [hs']
      exact w.asIdeal.zero_mem
    have h2 := Submodule.smul_mem (Submodule.span K (M : Set (Fin n → K))) ((s : K)⁻¹)
      (Submodule.subset_span hsx)
    convert h2 using 1
    funext i
    simp [Algebra.smul_def, hs0]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x j •
      (fun i => (B : Matrix (Fin n) (Fin n) K) i j) := by
    have hBx : (B : Matrix (Fin n) (Fin n) K).mulVec
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec]
      simp
    conv_lhs => rw [← hBx]
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)

variable {ι : Type} [Fintype ι] {a : ℕ}

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
omit [NumberField K] in

theorem _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv (lam : ι → _root_.Formalism.BasicNotions.DomWeight a)
    (B : ι → GL (Fin a) K) (F : _root_.Formalism.L2.DIV.Pol K ι a) :
    _root_.Formalism.L2.DIV.actP lam (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ F =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
        _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F := by
  have hg : ∀ τ, (((fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ τ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (B τ : Matrix (Fin a) (Fin a) K)ᵀ := fun τ => rfl
  simp only [_root_.Formalism.L2.DIV.actP, _root_.Formalism.L2.DIV.trAct, _root_.Formalism.L2.DIV.detTw_eq, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hg,
    Matrix.det_transpose, Matrix.transpose_transpose]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem valuation_coe_eq_one_of_notMem {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : w.valuation K (s : K) = 1 := by
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem exists_notMem_mul_eq_integer_of_valuation_le_one {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : w.valuation K x ≤ 1) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : 𝓞 K, (s : K) * x = (c : K) := by
  have h1 : x ∈ (w.valuation K).valuationSubring := hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
  have h3 : x ∈ (HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := h1
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h3
  have h2 : x ∈ _root_.GlobalTheory.LatBasisAt.locRing w := by
    unfold _root_.GlobalTheory.LatBasisAt.locRing
    exact h3
  obtain ⟨c, s, hs, rfl⟩ := (_root_.GlobalTheory.LatBasisAt.mem_locRing w x).1 h2
  refine ⟨s, hs, c, ?_⟩
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
  change algebraMap (𝓞 K) K s * (algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K s)⁻¹) =
    algebraMap (𝓞 K) K c
  field_simp

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in

theorem _root_.GlobalTheory.HAtBasis.mem_HAt_iff : ∀ (K : Type) [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) (B : ι → GL (Fin a) K),
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.LatWithBasis w M B → ∀ F : _root_.Formalism.L2.DIV.VV K lam,
      F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
        ∀ m, w.valuation K (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
          _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a)).coeff m) ≤ 1 := by
  intro K _ _ w ι _ a lam M B hMB F
  have hB' : ∀ τ, _root_.Formalism.L2.DIV.IsBasisAt w (_root_.Formalism.L2.DIV.dualFr (M τ)) (_root_.Formalism.BasicNotions.inside₂ K a (B τ)) :=
    fun τ => _root_.GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hMB τ).1 (hMB τ).2
  have hlat : ∀ τ, Submodule.IsLattice K (_root_.Formalism.L2.DIV.dualFr (M τ)) := fun τ =>
    _root_.GlobalTheory.DualLat.isLattice_dualFr _ (_root_.GlobalTheory.HAtBasis.isLattice_of_basisAt w (hMB τ).1 (hMB τ).2)
  have hloc := (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam
    (fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) hlat w (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ)) hB').1
  have step1 : F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
      (F : _root_.Formalism.L2.DIV.Pol K ι a) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.nabP lam fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt _root_.Formalism.L2.DIV.nabK
    rw [_root_.PI.LocGlobInclWork.mem_localization_iff, _root_.PI.LocGlobInclWork.mem_localization_iff]
    rfl
  rw [step1, hloc, _root_.GlobalTheory.TransLoc.mem_map_actP, _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  set G : _root_.Formalism.L2.DIV.Pol K ι a := (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
    _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a) with hG
  have hcoeff : ∀ (s : 𝓞 K) m, coeff m (s • G) = (s : K) * coeff m G := by
    intro s m
    erw [Algebra.smul_def, MvPolynomial.algebraMap_apply, coeff_C_mul]
  constructor
  · intro hGm m
    obtain ⟨s, hs, hsG⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).1 hGm
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hsG
    have hc : coeff m (s • G) = ((coeff m P : 𝓞 K) : K) := by
      have h' : coeff m (_root_.Formalism.L2.DIV.toK K _ P) = coeff m (s • G) := congrArg (coeff m) hP
      rw [← h']
      simp [_root_.Formalism.L2.DIV.toK, coeff_map]
    rw [hcoeff] at hc
    have hs0 : (s : K) ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
    have e : coeff m G = (s : K)⁻¹ * ((coeff m P : 𝓞 K) : K) := by
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, map_mul, map_inv₀, valuation_coe_eq_one_of_notMem w hs, inv_one, one_mul]
    exact HeightOneSpectrum.valuation_le_one w _
  · intro hint
    choose sf hsf c hc using fun m => exists_notMem_mul_eq_integer_of_valuation_le_one w _ (hint m)
    refine (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).2 ⟨∏ m ∈ G.support, sf m, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hsf m hm
    · have hGV : G ∈ _root_.Formalism.L2.DIV.VV K lam :=
        Submodule.smul_mem _ _ (_root_.Formalism.L2.DIV.ps_blockAct_mem_VV lam _ F.2)
      refine _root_.GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral K ι a lam (fun _ => 0) _
        (Submodule.smul_of_tower_mem _ _ hGV) fun m => ?_
      simp only [pow_zero, Finset.prod_const_one, one_mul]
      change IsIntegral ℤ (coeff m ((∏ m ∈ G.support, sf m) • G))
      rw [hcoeff]
      by_cases hm : m ∈ G.support
      · rw [← Finset.mul_prod_erase _ _ hm]
        push_cast
        rw [mul_comm ((sf m : 𝓞 K) : K), mul_assoc, hc m]
        have hI := RingOfIntegers.isIntegral_coe ((∏ i ∈ G.support.erase m, sf i) * c m)
        convert hI using 1
        simp
      · rw [notMem_support_iff.1 hm, mul_zero]
        exact isIntegral_zero

end GlobalTheory.HAtBasis
