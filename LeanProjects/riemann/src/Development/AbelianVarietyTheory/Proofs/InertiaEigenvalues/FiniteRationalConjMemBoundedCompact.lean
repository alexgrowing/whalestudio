import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Formalism.LocalToGlobal.IndefiniteReal.CongNatCastEqOneTmul
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open scoped TensorProduct

namespace GlobalTheory.StabFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem norm_entry_le_one {g : GL (Fin n) L} (hg : g ∈ GQ0 L n) (φ : L →+* ℂ) (i j : Fin n) :
    ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ≤ 1 := by
  have h0 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) g = 1 := hg
  have h1 := congrFun (congrFun h0 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h1
  have h2 := congrArg φ h1
  simp only [map_sum, map_mul, map_one] at h2
  have h3 : ∑ k, ((‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := IsCMField.complexEmbedding_complexConj L φ ((g : Matrix (Fin n) (Fin n) L) i k)
    rw [show ((IsCMField.complexConj L : L →+* L) ((g : Matrix (Fin n) (Fin n) L) i k)) =
      IsCMField.complexConj L ((g : Matrix (Fin n) (Fin n) L) i k) from rfl, this, Complex.mul_conj', Complex.ofReal_pow]
  have h4 : ∑ k, ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 = 1 := by exact_mod_cast h3
  have h5 : ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ ^ 2 ≤ 1 := by
    rw [← h4]
    exact Finset.single_le_sum (f := fun k => ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ ((g : Matrix (Fin n) (Fin n) L) i j))]

theorem exists_common_denom {ι : Type} [Fintype ι] (x : ι → AL L) :
    ∃ D : ℕ, 0 < D ∧ ∀ a, (D : AL L) * x a ∈ ALint L := by
  classical
  choose d hd0 hd using fun a => Formalism.IndefR.principalLevelFrame.cong_nat_denom (x a)
  refine ⟨∏ a, d a, Finset.prod_pos fun a _ => hd0 a, fun a => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Nat.cast_mul, mul_comm ((d a : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (hd a)

theorem exists_rat (γ : GQ L n) : ∃ g : GL (Fin n) L, g ∈ GQ0 L n ∧
    ∀ i j, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      ((g : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[L⁺] (1 : AFplus L) := by
  have h : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.1 h
  refine ⟨g, hg, fun i j => ?_⟩
  rw [← he]
  rfl

theorem isIntegral_of_mem (z : L) (hz : z ⊗ₜ[L⁺] (1 : AFplus L) ∈ ALint L) : IsIntegral ℤ z :=
  Formalism.UG.P.csGlob_int (F := L⁺) z (GlobalTheory.AlgFormsFin.ALint_le L hz)

end GlobalTheory.StabFin

open scoped TensorProduct

namespace GlobalTheory.StabFin

theorem finite_conj_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  intro L _ _ _ n J hJ t
  classical
  obtain ⟨F, hF⟩ := hJ
  let M : GAf L n → Matrix (Fin n) (Fin n) (AL L) := fun a => ((a : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨D, hD0, hD⟩ := exists_common_denom (L := L) (ι := (F × Fin n × Fin n) ⊕ (Fin n × Fin n))
    (fun a => match a with
      | .inl ⟨f, i, k⟩ => M (t * f) i k
      | .inr ⟨l, j⟩ => M t⁻¹ l j)
  have key : ∀ γ : GQ L n, t⁻¹ * (γ : GAf L n) * t ∈ J → ∀ i j, ((D : AL L) * D) * M γ i j ∈ ALint L := by
    intro γ hγ i j
    obtain ⟨f, hf, hu⟩ := hF _ hγ
    have hu' : ∀ a b, M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) a b ∈ ALint L := hu
    have e : (γ : GAf L n) = (t * f) * (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * t⁻¹ := by group
    have eM : M γ = M (t * f) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) * M t⁻¹ := by
      conv_lhs => rw [e]
      simp only [M, Subgroup.coe_mul, Units.val_mul]
    rw [eM, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have e2 : ((D : AL L) * D) * (M (t * f) i k * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * M t⁻¹ l j) =
        ((D : AL L) * M (t * f) i k) * M (f⁻¹ * (t⁻¹ * (γ : GAf L n) * t)) k l * ((D : AL L) * M t⁻¹ l j) := by ring
    rw [e2]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hD (.inl ⟨⟨f, hf⟩, i, k⟩)) (hu' k l)) (hD (.inr ⟨l, j⟩))
  set T : Set L := {z : L | IsIntegral ℤ z ∧ ∀ φ : L →+* ℂ, ‖φ z‖ ≤ ((D * D : ℕ) : ℝ)} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le L ℂ _
  have : Finite T := hTfin.to_subtype
  choose gs hgs0 hgs using exists_rat (L := L) (n := n)
  have hmem : ∀ x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J}, ∀ i j,
      ((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j ∈ T := by
    intro x i j
    refine ⟨isIntegral_of_mem _ ?_, fun φ => ?_⟩
    · have e : (((D * D : ℕ) : L) * (gs x.1 : Matrix (Fin n) (Fin n) L) i j) ⊗ₜ[NumberField.maximalRealSubfield L] (1 : AFplus L) =
          ((D : AL L) * D) * M x.1 i j := by
        simp only [M]
        rw [hgs, ← Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.includeLeftRingHom_apply,
          map_mul, map_natCast]
        push_cast; ring
      rw [e]
      exact key x.1 x.2 i j
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (norm_entry_le_one (hgs0 x.1) φ i j)
  refine Finite.of_injective (fun x => fun i j => (⟨_, hmem x i j⟩ : T)) ?_
  intro x y hxy
  have hD' : ((D * D : ℕ) : L) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD0 hD0).ne'
  have hg : ∀ i j, (gs x.1 : Matrix (Fin n) (Fin n) L) i j = (gs y.1 : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have := congrArg Subtype.val (congrFun (congrFun hxy i) j)
    exact mul_left_cancel₀ hD' this
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [hgs x.1 i j, hgs y.1 i j, hg i j]

end GlobalTheory.StabFin
