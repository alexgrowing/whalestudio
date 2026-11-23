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

namespace GlobalTheory.LevelSeries

theorem isIntegral_of_finAdele_valuation_le_one {E : Type} [Field E] [NumberField E] (x : E)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q) ≤ 1) :
    IsIntegral ℤ x := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E x fun Q => by
    have := h Q
    rwa [show (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q = (x : Q.adicCompletion E) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem map_fin_eq_of_isRat (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) (hR : GlobalTheory.Member.IsRat V γ γ') :
    Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1 =
      Matrix.GeneralLinearGroup.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) γ' := by
  have hf : (fin V γ).1 = finHom V γ := rfl
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  rw [hf]
  simp only [finHom, MonoidHom.comp_apply]
  rw [show matHom V γ = _ from hR]
  simp only [Formalism.UG.bc, Matrix.GeneralLinearGroup.map, incA, inclR, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe, Matrix.GeneralLinearGroup.map_apply]
  change ι ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (Algebra.TensorProduct.includeRight ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b))) = algebraMap D.host.E _ ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact h1 _

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem exists_coprime_isIntegral_of_bnd {E : Type} [Field E] [NumberField E] {n : ℕ} (l c : ℕ)
    (A : Matrix (Fin n) (Fin n) E)
    (h : GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 E) E)) •
      A.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)))) :
    ∃ m : ℕ, m.Coprime l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * A a b) := by
  obtain ⟨m, hm, hv⟩ := h
  refine ⟨m, hm, fun a b => isIntegral_of_finAdele_valuation_le_one _ fun Q => ?_⟩
  have := hv a b Q
  simpa [Matrix.smul_apply, Matrix.map_apply, map_mul, mul_assoc] using this

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem denomAt_of_isRat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → ∀ (V : HSp D) (l c : ℕ) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), GlobalTheory.Member.IsRat V γ γ' → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1).1) → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1)⁻¹.1) → DenomAt l c γ' := by
  intro D ι h1 V l c γ γ' hR hb1 hb2
  have hM := map_fin_eq_of_isRat D ι h1 V γ γ' hR
  rw [hM] at hb1 hb2
  rw [← map_inv] at hb2
  obtain ⟨m₁, hm₁, hi₁⟩ := exists_coprime_isIntegral_of_bnd l c (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb1
  obtain ⟨m₂, hm₂, hi₂⟩ := exists_coprime_isIntegral_of_bnd l c ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb2
  have hn : ∀ k : ℕ, IsIntegral ℤ (k : D.host.E) := fun k => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (k : ℤ)))
  refine ⟨m₁ * m₂, Nat.Coprime.mul hm₁ hm₂, fun a b => ⟨?_, ?_⟩⟩
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₂ : D.host.E) * ((((m₁ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₂).mul (hi₁ a b)
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₁ : D.host.E) * ((((m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₁).mul (hi₂ a b)

end GlobalTheory.LevelSeries
