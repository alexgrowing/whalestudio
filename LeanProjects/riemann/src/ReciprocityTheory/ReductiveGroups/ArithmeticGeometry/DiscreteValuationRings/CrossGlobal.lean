import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecZeroOfThickZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem cross_global (hLaws : Laws) (hL4 : Laws4) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))} (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ} (hk : 1 ≤ k)
    (s : Fin 2 → P.U.SecK k) (F : Fin 2 → Fam P.D.toPre (FractionRing V) k) (hs : ∀ i, P.U.Expands k (s i) (F i))
    (s'' : Fin 2 → P.U.SecK (k * N)) (F'' : Fin 2 → Fam P.D.toPre (FractionRing V) (k * N))
    (hs'' : ∀ i, P.U.Expands (k * N) (s'' i) (F'' i))
    (hPA : letI := H.starRing; ∀ i, PullAl P.D (FractionRing V) P.oD a k N (F i) (F'' i)) :
    ∀ j, (mulSec P.U.LG.L _ _ _ _ (s'' 0) (pullSec P.U.LG.L _ _ (s 1) (endK (t.act.act a)))).f j =
      (mulSec P.U.LG.L _ _ _ _ (s'' 1) (pullSec P.U.LG.L _ _ (s 0) (endK (t.act.act a)))).f j := by
  letI := H.starRing
  exact cross_global_of hLaws P a N hN hN0
    (fun e X hX uR huR huR0 hinj σ'' τ f'' f h'' hf hrel hoff =>
      cross_vanish hL4 P a k N e X hX uR huR huR0 hinj σ'' τ f'' f h'' hf hrel hoff)
    s F hs s'' F'' hs'' hPA

end ReciprocityTheory.ChartRestriction.G.DVR
