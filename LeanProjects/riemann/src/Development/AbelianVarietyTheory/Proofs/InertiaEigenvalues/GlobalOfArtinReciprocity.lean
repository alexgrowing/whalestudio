import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportValStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.StepGlobalPf

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chi_one_eq_one (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  have h1 : mapM (toK D.nd i) (rO D.nd i r π) γ = 1 := by
    simp [mapM, rO, hγ]
  simp only [h1, Matrix.one_mulVec, hu, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

theorem noChiOff (Xs : Set (D.nd.X i)) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : GlobalTheory.Cut.NoChiOff i r Xs := by
  intro x _ hxZ u hu
  by_contra hu0
  refine hxZ (hG6 x ⟨u, hu0, fun g => ?_⟩)
  have h := hu g
  rw [rTwO, mapM_twistM, Matrix.smul_mulVec] at h
  conv_rhs => rw [← h]
  rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    one_smul]

theorem unrOut (Xs : Set (D.nd.X i)) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    GlobalTheory.Cut.UnrOut i r Xs := by
  intro v hvl hvS hvQ x _ γ hγ
  have hχ := chi_one_eq_one i r ρ π hD (hG4 π v hvl hvS hvQ γ hγ)
  have hx : rO D.nd i r x γ = 1 := by simp [rO, hG4 x v hvl hvS hvQ γ hγ]
  rw [rTwO, twistM]
  simp [hx, hχ]

theorem atS (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.S i, (GlobalTheory.Cut.QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ GlobalTheory.Cut.PolyAt i r Xs π v := by
  intro v hv
  have hS := ((D.nd.S_def i v).1 hv).1
  have hv5 := hG5 v (Or.inl hv)
  have hv5x := hG5x v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hv5.2 hk hv hv5x.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hv5.1 (Or.inr hp)) x).1 γ hγ, hv5x.2.2.2 hv hp⟩

theorem atQ (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.Q i, GlobalTheory.Cut.QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1 := fun v hv =>
  ⟨fun x _ γ hγ => ((hG5 v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ, (hG5x v (Or.inr hv)).2.2.1 hv⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → StepGlobal := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha

end GlobalTheory.StepGlobalPf
