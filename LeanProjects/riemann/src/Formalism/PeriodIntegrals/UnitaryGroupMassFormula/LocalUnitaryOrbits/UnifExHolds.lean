import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct

theorem unifEx_holds {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    UnifEx v := by
  refine ⟨PI.VolStabSW.unifV v, ?_⟩
  unfold IsUnif
  rw [PI.VolStabSW.unifV_val]
  rfl

theorem unif_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : Fv F v)
    (hϖ : IsUnif v ϖ) : ϖ ≠ 0 ∧ Tendsto (fun k : ℕ => ϖ ^ k) atTop (𝓝 0) ∧
      ϖ ∈ v.adicCompletionIntegers F := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h1 : Valued.v ϖ < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

section Sub

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem oEv_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.add_mem _ hx hy

theorem oEv_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.zero_mem _

theorem oEv_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.neg_mem _ hx

def lamS (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def hermOE (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := by
    intro x y hx hy i j
    exact oEv_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oEv_zero v
  neg_mem' := by
    intro x hx i j
    exact oEv_neg v (hx i j)

def lamN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (TupV (E := E) v n a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (lamS v Λ a)

def hN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (hermOE σ v a)

def FibU' (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (LamT v Λ a) =
      dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def LamOC (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsOpen (LamT v Λ a) ∧ IsCompact (LamT v Λ a)

def HermOC (a : ℕ) : Prop :=
  IsOpen (hermOE σ v a : Set (HermR (Fv F v) σ a)) ∧ IsCompact (hermOE σ v a : Set (HermR (Fv F v) σ a))

def FibHens (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j),
    ∀ y ∈ LamT v Λ a, PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
        PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y ∈ hN σ v ϖ a 0 →
      ∃ D : TupV (E := E) v n a →+ HermR (Fv F v) σ a,
        (∀ k, (lamN v Λ ϖ a k).map D = hN σ v ϖ a k) ∧
        ∀ k, ∀ Z ∈ lamN v Λ ϖ a 0, ∀ W ∈ lamN v Λ ϖ a k,
          PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z + W) -
            PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈ hN σ v ϖ a (k + 1)

end Sub

end PI.OmLocU
