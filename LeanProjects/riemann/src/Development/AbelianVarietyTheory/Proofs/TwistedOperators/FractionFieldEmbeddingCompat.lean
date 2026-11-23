import Mathlib
import Formalism.LocalRingCardinality.DataNChTie
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion

noncomputable section

namespace GlobalTheory.Proof.FractionFieldEmbeddingCompat

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

theorem fracExt_fracBase_algebraMap {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
          (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y))) := by
  rw [← IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  simp [fracExt, fracBase, IsFractionRing.map]

theorem embW_eq_of_tie {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : D.LL0) :
    c.embW w (x : D.what₂.LL) = fracExt c w (fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) := by
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) (embSide D (c.twI w) (c.sd w) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have hmul : embSide D (c.twI w) (c.sd w) x * algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have e := h.embedding_baseField_condition w x y z hz0 hmul
  rw [← fracExt_fracBase_algebraMap, ← fracExt_fracBase_algebraMap, ← hmul, map_mul, map_mul] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 ((map_ne_zero _).2 hz1)) e

theorem embCompat : EmbCompat := by
  intro D c h K _ _ _ κ hκ w ιK hι
  subst hι
  ext x
  have e := embW_eq_of_tie h w (κ x)
  rw [hκ x] at e
  exact e

end GlobalTheory.Proof.FractionFieldEmbeddingCompat

end
