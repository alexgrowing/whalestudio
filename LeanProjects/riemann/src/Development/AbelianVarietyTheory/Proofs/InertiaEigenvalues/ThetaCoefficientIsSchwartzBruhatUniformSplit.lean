import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem symplO_nsmul_left_eq (S T : HSp D) (k : ℕ) (l x : WO S T) :
    symplO S T (k • l) x = symplO S T l (k • x) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, GlobalTheory.PlaceModel.symplO_zero_left, GlobalTheory.PlaceModel.symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, ih]

theorem coef_isSBHalf_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf
  classical
  have ha' := GlobalTheory.SplitScalar.isSplitIdem_conj ha
  have hd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hstc : ∀ u ∈ latH S T ΛS ΛT, cA D a • u ∈ latH S T ΛS ΛT := fun u hu =>
    GlobalTheory.SplitScalar.idem_smul_mem ha'.1 u hu
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  have hinv : ∀ u ∈ latH S T ΛS ΛT, heisO ψ S T (k • u) f = f := fun u hu =>
    hUf _ (hkU u hu) (GlobalTheory.SplitScalar.latO_fin ((latH S T ΛS ΛT).nsmul_mem hu k))
  have hsupp : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT := by
    intro ℓ hℓ x hx hne
    by_contra hn
    obtain ⟨l, hl, hlh, hlne⟩ := GlobalTheory.SplitScalar.exists_dual_half ha hd hstc
      (GlobalTheory.SplitScalar.isHalf_nsmul hx k) hn
    have h1 := hℓ (k • l) (GlobalTheory.SplitScalar.isHalf_nsmul hlh k) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x)
    rw [GlobalTheory.SplitScalar.heisO_comm, hinv l hl, map_smul, smul_eq_mul, symplO_nsmul_left_eq] at h1
    apply hlne
    have h2 : (ψ (symplO S T l (k • x)) - 1) * ℓ (heisO ψ S T x f) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  have hcoef : ∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f) := by
    intro ℓ hℓ
    refine ⟨fun t ht => ?_, k, hk, fun u hu huh t => ?_, fun t ht => ?_⟩
    · by_contra hn
      exact ht (by simp only [coef, if_neg hn])
    · by_cases htt : IsHalf a t
      · have h2 : IsHalf a (t + k • u) := GlobalTheory.SplitScalar.isHalf_add htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
        simp only [coef, if_pos htt, if_pos h2]
        rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
          (GlobalTheory.SplitScalar.half_orth ha htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu]
      · have h2 : ¬ IsHalf a (t + k • u) := fun h => htt (by
          have := GlobalTheory.SplitScalar.isHalf_sub h (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
          rwa [add_sub_cancel_right] at this)
        simp only [coef, if_neg htt, if_neg h2]
    · have htt : IsHalf a t := by
        by_contra hn
        exact ht (by simp only [coef, if_neg hn])
      refine hsupp ℓ hℓ t htt ?_
      simpa only [coef, if_pos htt] using ht
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.DiagLiftFix.half_finite_mod (S := S) (T := T) hS.1.fg hT.1.fg ha.1 (k * k)
    (Nat.mul_pos hk hk)
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk x, ← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hP : ((fun t : WO S T => k • t) ⁻¹' R).Finite := hR.preimage tf.injOn
  refine ⟨⟨k, hk, fun u hu _ => hinv u hu, hsupp⟩, hcoef, hP.toFinset.filter (fun x => IsHalf a x),
    fun x hx => (Finset.mem_filter.1 hx).2, fun x hx => ?_⟩
  by_cases hkx : k • x ∈ latH S T ΛS ΛT
  · right
    obtain ⟨r, hr, u, hu, e⟩ := hRm (k • x)
      ⟨hkx, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_nsmul hx k)⟩
    have huh : IsHalf a u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2
    have hxu : IsHalf a (x - k • u) := GlobalTheory.SplitScalar.isHalf_sub hx (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
    refine ⟨x - k • u, Finset.mem_filter.2 ⟨hP.mem_toFinset.2 ?_, hxu⟩, ?_⟩
    · show k • (x - k • u) ∈ R
      rwa [smul_sub, e, smul_smul, add_sub_cancel_right]
    · conv_lhs => rw [show x = (x - k • u) + k • u by abel]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
        (GlobalTheory.SplitScalar.half_orth ha hxu (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu.1]
  · left
    intro ℓ hℓ
    by_contra hne
    exact hkx (hsupp ℓ hℓ x hx hne)

end GlobalTheory.DownLift.SplitCoef

end
