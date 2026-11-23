import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GammaYOf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_lift_pt {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem qkYOnto (hM : MulNSt) : QkYOntoSt := by
  intro R _ _ _ D hB F _ _ _ n hn y
  obtain ⟨h₁, -, h₂, -⟩ := hM _ D.P n hn
  obtain ⟨b, hb⟩ := exists_lift_pt (mulA D.P.A n).left (cP D (TF (R := R) F) y).left
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  let b' : TF (R := R) F ⟶ D.P.A := Over.homMk b (by
    rw [← Over.w (mulA D.P.A n), ← Category.assoc, hb]; exact Over.w _)
  obtain ⟨q, hq, -⟩ := exists_qk_over (F := F) hJ hB hn y b' (Over.OverMorphism.ext (by
    rw [← hb, ← Category.comp_id b', ← MonObj.comp_pow]; rfl))
  exact ⟨q, hq⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
