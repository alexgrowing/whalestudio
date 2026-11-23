import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI

open Formalism.L2.Host

open Classical in
def EtaInfGen : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]
    (I : Type) [Fintype I] (φ : I → L →+* ℂ),
    (∀ w : InfinitePlace F, w.IsReal) →
    (∀ w : InfinitePlace F,
      (Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ aboveInf (L := L) F w)).card = 1) →
    ∀ (w : InfinitePlace F) (k : Fˣ),
      (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ aboveInf (L := L) F w),
        (φ i ((upF F k : Lˣ) : L) / ((‖φ i ((upF F k : Lˣ) : L)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
        ((etaInf F w k : ℂˣ) : ℂ)

end PI
