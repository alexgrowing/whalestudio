import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLevEq
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem filDim_of [NeZero n] (W : LocWach PD LL O v n) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := by
  intro hCA T hT i τ hOv
  have hK : Function.Bijective (algebraMap K₀ K) := hCA.1
  have hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i := hOv
  refine ⟨?_, ?_⟩
  · rw [rk_ιDi_eq W hK hQ T hT i τ hτ]
    exact ((hQ hK T.V T.ρ hT).2 τ).2.1
  · intro a b hab
    rw [rk_filLev_eq W hK hQ T hT i τ hτ a, rk_filLev_eq W hK hQ T hT i τ hτ b]
    exact (rk_sum_multV (PD := PD) (ρ := T.ρ) (τ := τ) (m := a) (k := b) (hmk := hab)).symm

end Formalism.MainNotions.N.Pv.LocalLengthBound
