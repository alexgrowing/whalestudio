import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd

open GlobalTheory.SplitCongNbhd in

theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
