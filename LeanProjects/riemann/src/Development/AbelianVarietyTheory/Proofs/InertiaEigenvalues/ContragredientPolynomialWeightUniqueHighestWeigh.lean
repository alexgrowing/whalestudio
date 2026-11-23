import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Irr

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]

theorem pair_inv (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (γ : ReciprocityTheory.Aut.GQ L n) (x y : VV ℂ lam) :
    pairBK lam (mtRep emb lam γ x) (tenRep emb lam γ y) = pairBK lam x y :=
  (pairBK_apply lam _ _).trans ((pairingBInvariantK_holds ℂ ι n lam (mtwEmb emb (mtwRat γ)) (x : VV ℂ lam).1
    (y : VV ℂ lam).1).trans (pairBK_apply lam x y).symm)

theorem tenIrr_conj (emb : ι → L →+* ℂ) (lam : ι → DomWeight n) (h : TenIrr emb lam) :
    TenIrr (mtwConj emb) lam := by
  unfold TenIrr
  rw [mtRep_eq_tenRep, mtwConj_conj]
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hd := GlobalTheory.WtDual.dual_isIrreducible (mtRep emb lam) h
  let Φ : VV ℂ lam →ₗ[ℂ] Module.Dual ℂ (VV ℂ lam) := (pairBK lam).flip
  have hΦ : ∀ x y, Φ y x = pairBK lam x y := fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact (pairingBNondegenerate_holds ℂ ι n lam).2 y fun x => by
      rw [← hΦ, hy]
      rfl
  have hdim : Module.finrank ℂ (VV ℂ lam) = Module.finrank ℂ (Module.Dual ℂ (VV ℂ lam)) :=
    (Subspace.dual_finrank_eq).symm
  let E := LinearMap.linearEquivOfInjective Φ hinj hdim
  have hE : ∀ y, E y = Φ y := fun y => rfl
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam).dual (tenRep emb lam) E.symm
    (fun g f => ?_) hd
  apply E.injective
  rw [LinearEquiv.apply_symm_apply, hE]
  obtain ⟨y, rfl⟩ := E.surjective f
  rw [LinearEquiv.symm_apply_apply, hE]
  ext x
  rw [hΦ, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hΦ]
  have := pair_inv emb lam g ((mtRep emb lam g⁻¹) x) y
  rw [Representation.self_inv_apply] at this
  exact this

end Irr
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Omega

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)

def bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
  Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge

theorem bC_apply (i : VVIdx lam) : bC e lam i = mapVV e lam (bVV K lam i) := by
  simp [bC]

variable {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def omegaV : Module.Dual K W →ₛₗ[e] Module.Dual ℂ (VV ℂ lam) where
  toFun f := (bC e lam).constr ℂ fun i => e (f (T.symm (bVV K lam i)))
  map_add' f g := by
    rw [← map_add]
    congr 1
    funext i
    simp
  map_smul' c f := by
    rw [← map_smul]
    congr 1
    funext i
    simp

theorem omegaV_bC (f : Module.Dual K W) (i : VVIdx lam) :
    omegaV e lam T f (bC e lam i) = e (f (T.symm (bVV K lam i))) := by
  simp [omegaV, Module.Basis.constr_basis]

theorem omegaV_mapVV (f : Module.Dual K W) (x : VV K lam) :
    omegaV e lam T f (mapVV e lam x) = e (f (T.symm x)) := by
  conv_lhs => rw [← (bVV K lam).sum_repr x]
  conv_rhs => rw [← (bVV K lam).sum_repr x]
  simp only [map_sum, LinearMap.map_smulₛₗ, ← bC_apply, LinearMap.map_smul, omegaV_bC, smul_eq_mul, map_mul, RingHom.id_apply, LinearEquiv.map_smul, LinearMap.map_smul]

end Omega
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

section Props

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ) (lam : ι → DomWeight n)
  {W : Type} [AddCommGroup W] [Module K W] (T : W ≃ₗ[K] VV K lam)

def coordK : Module.Dual K W →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval K W (T.symm (bVV K lam i))

def coordC : Module.Dual ℂ (VV ℂ lam) →ₗ[ℂ] VV ℂ lam :=
  (bC e lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun i => Module.Dual.eval ℂ (VV ℂ lam) (bC e lam i)

theorem coordK_ker : LinearMap.ker (coordK lam T) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have h1 : ∀ i, f (T.symm (bVV K lam i)) = 0 := by
    intro i
    have h0 := congrArg (bVV K lam).equivFun hf
    simp only [coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero] at h0
    simpa using congrFun h0 i
  have h2 : f ∘ₗ T.symm.toLinearMap = 0 := (bVV K lam).ext fun i => by simpa using h1 i
  ext w
  have := LinearMap.congr_fun h2 (T w)
  simpa using this

theorem coordC_omegaV (f : Module.Dual K W) : coordC e lam (omegaV e lam T f) = mapVV e lam (coordK lam T f) := by
  simp only [coordC, coordK, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    LinearMap.pi_apply, Module.Dual.eval_apply, map_sum, LinearMap.map_smulₛₗ, omegaV_bC, bC_apply, omegaV_mapVV]

theorem omegaV_li (κ : Type) (v : κ → Module.Dual K W) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun x => omegaV e lam T (v x) := by
  refine LinearIndependent.of_comp (coordC e lam) ?_
  refine LinearIndependent.of_comp (VV ℂ lam).subtype ?_
  have h1 : LinearIndependent K fun x => ((coordK lam T (v x) : VV K lam) : Pol K ι n) :=
    (hv.map' (coordK lam T) (coordK_ker lam T)).map' (VV K lam).subtype (Submodule.ker_subtype _)
  convert Formalism.L2.Col.linearIndependent_map e _ h1 using 1
  funext x
  simp [coordC_omegaV, mapVV_coe]

theorem omegaV_coord (i : VVIdx lam) :
    omegaV e lam T ((bVV K lam).coord i ∘ₗ T.toLinearMap) = (bC e lam).coord i := by
  refine (bC e lam).ext fun j => ?_
  rw [omegaV_bC]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

theorem omegaV_span : Submodule.span ℂ (Set.range (omegaV e lam T)) = ⊤ := by
  classical
  rw [eq_top_iff, ← (bC e lam).dualBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨_, by rw [omegaV_coord, Module.Basis.coe_dualBasis]⟩

end Props
end GlobalTheory.MtContraHw

namespace GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col

theorem omegaV_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type}
    [Field K] (e : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam)
    (hT : ∀ γ x, T (ρ γ x) = rhoVr emb lam (mtwRat γ) (T x)) (γ : ReciprocityTheory.Aut.GQ L n) (f : Module.Dual K W) :
    omegaV e lam T (ρ.dual γ f) = (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) := by
  refine (bC e lam).ext fun j => ?_
  have h1 : (mtRep (fun t => e.comp (emb t)) lam).dual γ (omegaV e lam T f) (bC e lam j) =
      omegaV e lam T f (mapVV e lam (rhoVr emb lam (mtwRat γ⁻¹) (bVV K lam j))) := by
    rw [GlobalTheory.ConjTwist.mapVV_rhoVr, bC_apply]
    rfl
  rw [h1, bC_apply, omegaV_mapVV, omegaV_mapVV]
  show e (f (ρ γ⁻¹ (T.symm (bVV K lam j)))) = _
  congr 2
  apply T.injective
  rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.MtContraHw

open GlobalTheory.CoefModel Formalism.L2.Col in

theorem GlobalTheory.mtRatDual_hw : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm c hc lam hten W _ _ _ ρ T hT t lam0 hw
  have h' := GlobalTheory.MtContraHw.tenIrr_conj (fun t => e.comp (emb t)) lam hten
  have hwa := GlobalTheory.hwAt_of_hwAtF L n K e c hc (Module.Dual K W) ρ.dual
    (GlobalTheory.WtDual.dualWt (mtWt (fun t => e.comp (emb t)) lam hten)) (GlobalTheory.MtContraHw.omegaV e lam T)
    (GlobalTheory.MtContraHw.omegaV_li e lam T) (GlobalTheory.MtContraHw.omegaV_span e lam T)
    (GlobalTheory.MtContraHw.omegaV_comm e emb lam ρ T hT) (emb t) lam0 hw
  exact mtWt_hw_dual (fun t => e.comp (emb t)) hinj hcm lam hten h' t _ lam0 (GlobalTheory.WtDual.isDual_dualWt _) hwa
