import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

theorem form_placeModel_eq_zero_of_vanish : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a b : AE D, IsSplitIdem D a → b * b = b → b * cA D b = 0 → infPart D b = 0 → b * a = a → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b (latH S T ΛS ΛT) 1 f₀ Tm → ∀ ℓ, InvForm ψ S T a ℓ → ∀ Ψ : WO S T → ℂ, IsSBHalf b (latH S T ΛS ΛT) Ψ → (∀ t : WO S T, a • t = 0 → Ψ t = 0) → ℓ (Tm Ψ) = 0 := by
  intro D ψ S T hψ ΛS ΛT hS hT a b ha hbb hbc hbinf hba f₀ Tm hf₀ hTm ℓ hℓ Ψ hΨ hΨ0
  have hth : ∀ Ψ', IsSBHalf b (latH S T ΛS ΛT) Ψ' → IsThetaFunO ψ S T (Tm Ψ') := by
    intro Ψ' h'
    have hspan := (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT hbb hbc hbinf hTm h').1
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨u, rfl⟩
      exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ u
    · exact Formalism.IndefR.Fock.CCR.theta_zero ψ S T
    · intro x y _ _ hx hy
      exact Formalism.IndefR.Fock.CCR.theta_add hx hy
    · intro c x _ hx
      exact Formalism.IndefR.Fock.CCR.theta_smul hx c
  have hca : cA D b * cA D a = cA D a := by rw [← RingHom.map_mul, hba]
  have hmod : ∀ y, IsHalf (cA D a) y → ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) = ℓ (Tm Ψ) := by
    intro y hy
    have hy' : IsHalf (cA D b) y := fun i j => by rw [← hy i j, ← mul_assoc, hca]
    rw [hTm.modul Ψ hΨ y hy']
    exact hℓ y hy _ (hth Ψ hΨ)
  obtain ⟨k, hk, hinv, hden⟩ := hΨ.2
  have hcomm : ∀ (c : AE D) (x : WO S T), c • (k • x) = k • (c • x) := fun c x =>
    map_nsmul (DistribMulAction.toAddMonoidHom (WO S T) c) k x
  have haa : a * a = a := ha.1
  have hainf : infPart D a = 0 := GlobalTheory.SplitScalar.infPart_splitIdem ha
  obtain ⟨Y, hYne, hY1, -, hY3⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ ΛS ΛT hS hT a haa hainf k hk
  have hzero : (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t) = 0 := by
    funext t
    simp only [Pi.zero_apply]
    by_cases ht : Ψ t = 0
    · simp [ht]
    rw [← Finset.sum_mul]
    have hsym : ∀ y ∈ Y, symplO S T t y = symplO S T (a • t) y := by
      intro y hy
      rw [GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 (hY1 y hy).1]
    have hx : IsHalf a (a • t) := (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, haa])
    have hkx : k • (a • t) ∈ latH S T ΛS ΛT := by
      rw [← hcomm a t]
      exact GlobalTheory.SplitScalar.idem_smul_mem haa _ (hden t ht)
    obtain ⟨-, h2⟩ := hY3 (a • t) hx hkx
    by_cases hex : ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ a • t = k • u
    · exfalso
      obtain ⟨u, hu, hau, hxu⟩ := hex
      have hbu : IsHalf b u := fun i j => by rw [← hau i j, ← mul_assoc, hba]
      have e1 : Ψ (t - k • u + k • u) = Ψ (t - k • u) := hinv u hu hbu (t - k • u)
      rw [sub_add_cancel] at e1
      apply ht
      rw [e1]
      apply hΨ0
      rw [smul_sub, hxu, hcomm a u, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hau, sub_self]
    · rw [Finset.sum_congr rfl fun y hy => by rw [hsym y hy], h2 hex, zero_mul]
  have hsum : ∑ y ∈ Y, ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) =
      ℓ (Tm (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t)) := by
    rw [← map_sum ℓ, ← map_sum Tm]
    congr 2
    funext t
    simp [Finset.sum_apply]
  rw [hzero, map_zero, map_zero, Finset.sum_congr rfl fun y hy => hmod y (hY1 y hy).1, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hYne.card_pos.ne'
  exact (mul_eq_zero.1 hsum).resolve_left hc

end GlobalTheory.DownLift.SplitCoef

end
