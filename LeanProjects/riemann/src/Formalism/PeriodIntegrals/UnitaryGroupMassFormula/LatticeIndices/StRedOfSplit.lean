import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev Op (p : TypX X) : Type := p.1.adicCompletionIntegers X.B.I.F

def StResZ (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}

def StLatGL (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      ∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p

theorem stRed_of_split (p : TypX X) (hR : StResZ X p) (hL : StLatGL X p) : StRed X p := by
  classical
  intro K hK
  obtain ⟨π, hπs, hπk⟩ := hR
  obtain ⟨ψ, hψs, hψ⟩ := hL K hK
  refine ⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩
  · intro N
    have hsi : ∀ b, π (Function.surjInv hπs b) = b := Function.surjInv_eq hπs
    let M' : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
      fun i j => Function.surjInv hπs ((N : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)
    have hM' : ∀ i j, π (M' i j) = (N : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j := fun i j => hsi _
    have hdet : π M'.det = (N : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact hM' i j
    obtain ⟨e, he⟩ := (Matrix.isUnits_det_units N).exists_right_inv
    have h1 : π (M'.det * Function.surjInv hπs e) = 1 := by
      rw [map_mul, hdet, hsi, he]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (M'.det * Function.surjInv hπs e) with hu | hu
    · have hd : IsUnit M'.det := isUnit_of_mul_isUnit_left hu
      have hM : IsUnit M' := (Matrix.isUnit_iff_isUnit_det M').mpr hd
      obtain ⟨k, hk⟩ := hψs hM.unit
      refine ⟨k, ?_⟩
      apply Units.ext
      ext i j
      rw [MonoidHom.comp_apply, hk, Matrix.GeneralLinearGroup.map_apply, IsUnit.unit_spec]
      exact hM' i j
    · have h0 : IsUnit (π (1 - M'.det * Function.surjInv hπs e)) := hu.map π
      rw [map_sub, map_one, h1, sub_self] at h0
      haveI : Subsingleton (ZMod (gOf p)) := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
      refine ⟨1, ?_⟩
      apply Units.ext
      ext i j
      exact Subsingleton.elim _ _
  · intro x
    rw [← hψ x]
    have key : ∀ i j, ((((Matrix.GeneralLinearGroup.map π).comp ψ) x : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :
        Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j - (1 : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j =
        π ((((ψ x : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) := by
      intro i j
      rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.sub_apply, map_sub,
        Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    constructor
    · intro h i j
      rw [← hπk, RingHom.mem_ker, ← key, h]
      simp
    · intro h
      apply Units.ext
      ext i j
      have hij := h i j
      rw [← hπk, RingHom.mem_ker, ← key, sub_eq_zero] at hij
      simpa using hij

end Loc

end MassDataIdxSteps
