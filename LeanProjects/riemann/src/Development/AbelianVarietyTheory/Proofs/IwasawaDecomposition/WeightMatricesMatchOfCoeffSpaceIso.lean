import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.CoefMatch

theorem vvmatch_repr {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (y : VV K lam) (i : VVIdx lam) :
    (Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge).repr (mapVV φ lam y) i = φ ((bVV K lam).repr y i) := by
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  have hy : mapVV φ lam y = ∑ k, φ ((bVV K lam).repr y k) • B' k := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  rw [hy, Module.Basis.repr_sum_self]

theorem wtMatch_of_coef : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam), (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam), (∀ γ x, T' (ρ' γ x) = rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat γ) (T' x)) → GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' := by
  intro L _ _ _ n ι _ K _ φ emb lam W₀ W' _ _ _ _ ρ₀ ρ' T hT T' hT'
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge with hB'
  refine ⟨VVIdx lam, inferInstance, inferInstance, (bVV K lam).map T.symm, B'.map T'.symm, fun γ => ?_⟩
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [hT', hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hj : B' j = mapVV φ lam (bVV K lam j) := Module.Basis.mk_apply _ _ _
  rw [hj, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hB', vvmatch_repr]

end GlobalTheory.CoefMatch
