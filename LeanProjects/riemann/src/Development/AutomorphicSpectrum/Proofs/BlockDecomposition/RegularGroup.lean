import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedSatake

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaceBlocks

variable {K : Type} [Field K] [NumberField K]

def vOf (w : PlK K) : Pl :=
  ⟨w.asIdeal.under (𝓞 ℚ), inferInstance, Ideal.under_ne_bot (𝓞 ℚ) w.ne_bot⟩

theorem vOf_liesOver (w : PlK K) : w.asIdeal.LiesOver (vOf w).asIdeal := ⟨rfl⟩

theorem liesOver_iff (w : PlK K) (v : Pl) : w.asIdeal.LiesOver v.asIdeal ↔ vOf w = v := by
  constructor
  · intro h
    exact HeightOneSpectrum.ext h.over.symm
  · rintro rfl
    exact vOf_liesOver w

theorem finite_over (v : Pl) : {w : PlK K | w.asIdeal.LiesOver v.asIdeal}.Finite := by
  have hf := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine Set.Finite.of_finite_image (f := fun w : PlK K => w.asIdeal) (hf.subset ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  · intro w _ w' _ h
    exact HeightOneSpectrum.ext h

def fib (K : Type) [Field K] [NumberField K] (v : Pl) : Finset (PlK K) := (finite_over v).toFinset

theorem mem_fib {v : Pl} {w : PlK K} : w ∈ fib K v ↔ vOf w = v := by
  rw [fib, Set.Finite.mem_toFinset, Set.mem_setOf_eq, liesOver_iff]

theorem finprod_fib {M : Type*} [CommMonoid M] (f : PlK K → M) (v : Pl) :
    ∏ᶠ w : {w : PlK K // w.asIdeal.LiesOver v.asIdeal}, f w.1 = ∏ w ∈ fib K v, f w := by
  exact (finprod_set_coe_eq_finprod_mem (f := f) {w : PlK K | w.asIdeal.LiesOver v.asIdeal}).trans
    (finprod_mem_eq_finite_toFinset_prod f (finite_over (K := K) v))

theorem lfV_eq (DK : DatK K) (c : HeckeCharacter K) (v : Pl) (s : ℂ) :
    lfV DK c v s = ∏ w ∈ fib K v, lf3 (DK.ν w) (localChar c w) s :=
  finprod_fib (fun w : PlK K => lf3 (DK.ν w) (localChar c w) s) v

end GlobalTheory.CompanionTheory.PlaceBlocks
