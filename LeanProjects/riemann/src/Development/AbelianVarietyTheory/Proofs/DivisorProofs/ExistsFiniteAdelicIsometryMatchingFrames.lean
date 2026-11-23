import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIsoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.FinIsoExists

theorem exists_isometry {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (σ : A →+* A) {n n' : ℕ} (h : n = n')
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n') (Fin n') A) (β : GL (Fin n) A) (β' : GL (Fin n') A)
    (u : GL (Fin n) R) (u' : GL (Fin n') R)
    (hu : Formalism.UG.cT σ (β * Formalism.UG.bc φ u).val * J * (β * Formalism.UG.bc φ u).val = 1)
    (hu' : Formalism.UG.cT σ (β' * Formalism.UG.bc φ u').val * J' * (β' * Formalism.UG.bc φ u').val = 1) :
    ∃ u₀ : GL (Fin n') R, ∀ y : GL (Fin n') R, β' * Formalism.UG.bc φ y * β'⁻¹ ∈ Formalism.UG.UJ σ J' →
      ∃ (j : Matrix (Fin n') (Fin n) A) (j' : Matrix (Fin n) (Fin n') A), j * j' = 1 ∧ j' * j = 1 ∧
        Formalism.UG.cT σ j * J' * j = J ∧ j * β.val = (β' * Formalism.UG.bc φ (y * u₀)).val.submatrix id (Fin.cast h) := by
  subst h
  refine ⟨u' * u⁻¹, fun y hy => ?_⟩
  set k := β' * Formalism.UG.bc φ y * β'⁻¹ with hk
  set B := β * Formalism.UG.bc φ u with hB
  set B' := β' * Formalism.UG.bc φ u' with hB'
  have hy' : Formalism.UG.cT σ k.val * J' * k.val = J' := hy
  refine ⟨(k * B' * B⁻¹).val, (k * B' * B⁻¹)⁻¹.val, Units.mul_inv _, Units.inv_mul _, ?_, ?_⟩
  · calc Formalism.UG.cT σ (k * B' * B⁻¹).val * J' * (k * B' * B⁻¹).val
        = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B'.val * (Formalism.UG.cT σ k.val * J' * k.val) * B'.val) * B⁻¹.val := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ B⁻¹.val * (Formalism.UG.cT σ B.val * J * B.val) * B⁻¹.val := by rw [hy', hu, hu']
      _ = Formalism.UG.cT σ (B.val * B⁻¹.val) * J * (B.val * B⁻¹.val) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have e : k * B' * B⁻¹ * β = β' * Formalism.UG.bc φ (y * (u' * u⁻¹)) := by
      rw [hk, hB, hB', map_mul, map_mul, map_inv]
      group
    rw [← Units.val_mul, e]
    rfl

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := by
    rw [mem_blockTri]
    intro i j hij
    simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  rfl

theorem exists_isFinIso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (β' : GL (Fin V'.rank) (EAf D)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N' : ℕ) (Pg : Finset (Pl D.host.E)), V.rank = V'.rank → IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP') → ∃ j Φ, IsFinIso V V' β β' Pg j Φ := by
  intro D V V' β Λ N β' Λ' N' Pg h hβ hβ' hPg
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V β Λ N hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_integral_change_baseFrame_orthonormal V' β' Λ' N' hβ'
  obtain ⟨u₀, hu₀⟩ := exists_isometry (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h _ _ β β' u u' hu hu'
  have hL := GlobalTheory.T.finite_group_lifts_to_parahoric_level V' β' (datW V'.rank Pg (LevelP.triv Pg V'.rank ℂ) Frm.B) Λ' N' hβ' rfl hPg
  obtain ⟨κ, -, hκ, hred⟩ := hL (fun PP => (Formalism.UG.bc (resS D.host.F PP.1) u₀)⁻¹)
  obtain ⟨y, hy⟩ := parLev_St hκ
  have hU : β' * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype y * β'⁻¹ ∈
      UA D.sp.cm V'.gram := by
    have h1 := parLev_UA hκ
    rw [← hy] at h1
    exact h1
  obtain ⟨j, j', h1, h2, h3, h4⟩ := hu₀ y hU
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso V V' j j' h1 h2 h3
  refine ⟨j, Φ, h3, hΦ, h, y * u₀, h4, fun PP hPP => ?_⟩
  have h5 : upperLeftBlock le_rfl (redFn β' PP (finE V' κ)) = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ := congrFun hred ⟨PP, hPP⟩
  have h6 : redFn β' PP (finE V' κ) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (redFn β' PP) hy).symm.trans (redFn_frGL β' PP y)
  have h7 : Formalism.UG.bc (resS D.host.F PP) y = (Formalism.UG.bc (resS D.host.F PP) u₀)⁻¹ :=
    h6.symm.trans ((restrictedBlock_self_apply _ _).symm.trans h5)
  exact (map_mul _ y u₀).trans (mul_eq_one_iff_eq_inv.2 h7)

end GlobalTheory.FinIsoExists
