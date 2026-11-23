import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.InfTypeChar

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

open Classical in

def InfChar {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∃ Φ : Ideles L →* ℂˣ, Continuous Φ ∧ (∀ x, ‖((Φ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ v x, Φ (localIdele L v x) = 1) ∧
    (∀ k : Lˣ, ((Φ (diagUnits L k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧
    ∀ (S : Finset (InfinitePlace L)) (k : Lˣ), ((Φ (∏ w ∈ S, infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
      ∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ S), (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

end PI.InfTypeChar

namespace PI

def InfTypeChar : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ),
    InfTypeChar.InfChar φ n

end PI
