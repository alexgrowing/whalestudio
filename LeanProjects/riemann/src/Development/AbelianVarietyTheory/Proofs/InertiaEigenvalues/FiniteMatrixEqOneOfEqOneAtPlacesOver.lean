import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanInverseThetaIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.FinOneAt

set_option maxHeartbeats 1600000 in

theorem oneAt_fin_eq_one : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (HeightOneSpectrum.under (𝓞 D.host.F) P) - algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) P)) k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v ((ι (a ⊗ₜ[D.host.F] 1)) P - algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → ∀ (V : HSp D) (l : ℕ) (z : GA D V), OneAt V l z → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι hι hint happ V l z hz Q hlQ i j
  let α : Af D.host.F := singleV D.host.F (Q.under (𝓞 D.host.F)) 1
  have hε : IsPlaceIdem D (Q.under (𝓞 D.host.F)) (pairA D.host.F 0 α) :=
    ⟨α, rfl, GlobalTheory.PlaceIdem.single_same _, fun v' h => GlobalTheory.PlaceIdem.single_ne h⟩
  have hlv : ((l : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) Q.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hlQ
  have h0 := hz _ _ hε hlv i j
  have hα : ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) Q = 1 := by
    change ι (α ⊗ₜ[D.host.F] (1 : D.host.E)) Q = 1
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ α 1 Q n (by
      rw [map_one, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h1 : ι (finPart D ((Formalism.L2.Theta.mt V z - 1) i j)) Q = 0 := by
    have := congrArg (fun x => ι (finPart D x) Q) h0
    simp only [map_mul, map_zero] at this
    rw [GlobalTheory.PlaceIdem.mul_ap, hα, one_mul] at this
    exact this
  have hm : ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) = ι (finPart D (Formalism.L2.Theta.mt V z i j)) := rfl
  rw [hm]
  rw [Matrix.sub_apply, map_sub, map_sub] at h1
  refine (sub_eq_zero.1 h1).trans ?_
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    exact congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) (map_zero ι)

end GlobalTheory.LevelSeries.FinOneAt
