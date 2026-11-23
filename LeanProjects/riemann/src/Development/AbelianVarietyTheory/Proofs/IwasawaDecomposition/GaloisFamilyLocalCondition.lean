import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeckePointUniq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem eq_of_eigen : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i V hV x x' hx hx'
  classical
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hry : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (by rw [h, map_zero]))
  have hιinj : Function.Injective (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
      (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) :=
    ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp (Sp.iq i).injective).comp
      (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i)))
  have key : ∀ v k, SplitOut X.nd i v → 1 ≤ k → k ≤ D.R.nV →
      (X.nd.hT i v k : X.nd.X i → X.nd.O i) x = (X.nd.hT i v k : X.nd.X i → X.nd.O i) x' := by
    intro v k hv hk1 hk2
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    have e1 := hx v k s ϖ hv hc hu hk1 hk2 y hyV
    have e2 := hx' v k s ϖ hv hc hu hk1 hk2 y hyV
    rw [e1] at e2
    exact hιinj (smul_left_injective ℂ hry e2)
  have hTle : X.nd.T i ≤ AlgHom.equalizer (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x)
      (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x') := by
    rw [← X.nd.T_gen i]
    refine Algebra.adjoin_le ?_
    rintro f ⟨v, k, h1, h2, h3, h4, hk1, hk2, rfl⟩
    exact key v k ⟨h1, h2, h3, h4⟩ hk1 hk2
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := X.nd.T_sep i x x' hne
  exact hfx (hTle hf)

end GlobalTheory.HeckePointUniq
