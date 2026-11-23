import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem typesOpen_withLoc : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : AutSpec A M tp.tup Sp.iq L.Y L.C), (∀ σ lam, IsSSRep (L.Z.rbar σ lam)) → Nonempty (TypesOpen (withLoc L) jE) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big L Sp Au hss
  refine ⟨{ grp := ?_, par := ?_, plB := A.pl.plB, plκ := A.pl.plκ, plB_loc := ?_, plB_iota := ?_, rbarSS := ?_, rbar := ?_ }⟩
  · exact ⟨A.grp.tA, A.grp.tκ, A.grp.teichC_def, A.grp.ζ, A.grp.ζ_gen, A.grp.O, A.grp.eSer_def, A.grp.kv, A.grp.tg_tame, A.grp.O_equiv, A.grp.O_tw⟩
  · exact ⟨A.par.eM, A.par.eM_K, A.par.eP, A.par.locPar_def⟩
  · exact Au.kFbar
  · exact fun i k v x => A.iota _ k v x
  · exact fun σ lam _ => hss σ lam
  · exact fun i σ _ _ Sig ρ hP hR g => (L.rbar_tie i σ Sig ρ hP hR).2 g

end GlobalTheory.HeightCounting
