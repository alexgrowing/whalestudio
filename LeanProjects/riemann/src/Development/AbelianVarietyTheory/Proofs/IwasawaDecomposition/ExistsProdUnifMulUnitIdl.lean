import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.IdlFact

variable {L : Type} [Field L] [NumberField L]

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_apply (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) :
    valAt w a = Valued.v ((a : AdeleRing (𝓞 L) L).2 w) := rfl

theorem valAt_ne_zero (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a ≠ 0 :=
  ((Group.isUnit a).map (valAt w)).ne_zero

theorem valAt_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    valAt v (localIdele L v x) = Valued.v (x : v.adicCompletion L) := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
    have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h]

theorem valAt_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
    have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h, map_one]

theorem finite_valAt_ne_one (a : Ideles L) : {v | valAt v a ≠ 1}.Finite := by
  have hu : IsUnit ((a : AdeleRing (𝓞 L) L).2) :=
    a.isUnit.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  exact (FiniteAdeleRing.isUnit_iff.1 hu).2

open Classical in
theorem valAt_prod (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ)
    (w : HeightOneSpectrum (𝓞 L)) :
    valAt w (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) =
      WithZero.exp (-(if w ∈ S then n w else 0)) := by
  rw [map_prod]
  have h1 : ∀ v, v ≠ w → valAt w (localIdele L v (atFin v (unif v)) ^ n v) = 1 := fun v hv => by
    rw [map_zpow, valAt_localIdele_ne hv.symm, one_zpow]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w hw (fun v _ hv => h1 v hv), map_zpow, valAt_localIdele_self]
    have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    rw [h2, ← WithZero.exp_zsmul]
    simp
  · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
    simp

end GlobalTheory.Mem.Chr.IdlFact

open GlobalTheory.Mem.Chr.IdlFact in
open Classical in

theorem GlobalTheory.Mem.Chr.exists_prod_unif_mul_unitIdl : ∀ (L : Type) [Field L] [NumberField L] (a : Ideles L), ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ) (u : Ideles L), u ∈ unitIdl L ∧ a = (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) * u ∧ ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = WithZero.exp (-(if v ∈ S then n v else 0)) := by
  intro L _ _ a
  let S := (finite_valAt_ne_one a).toFinset
  let n : HeightOneSpectrum (𝓞 L) → ℤ := fun v => -WithZero.log (valAt v a)
  have hv : ∀ v, valAt v a = WithZero.exp (-(if v ∈ S then n v else 0)) := fun v => by
    split_ifs with h
    · simp only [n, neg_neg]
      exact (WithZero.exp_log (valAt_ne_zero v a)).symm
    · have : valAt v a = 1 := by simpa [S] using h
      rw [this]; simp
  refine ⟨S, n, (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v)⁻¹ * a, fun v => ?_, ?_, hv⟩
  · rw [← valAt_apply, map_mul, map_inv, valAt_prod, hv v]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero
  · rw [mul_inv_cancel_left]
