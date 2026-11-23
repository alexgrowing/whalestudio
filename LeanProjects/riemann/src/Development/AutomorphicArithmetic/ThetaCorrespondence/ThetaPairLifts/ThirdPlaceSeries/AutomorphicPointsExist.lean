import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicities
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutPts
end GlobalTheory.AutPts
namespace GlobalTheory.AutPts
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem automorphic_points_exist : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → (∀ x, ∃ P, ptV P = some x) ∧ ∀ x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV P = some x}, ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind
    htop ptV hpt
  classical
  have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hj1 : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  let B := gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)
  have hprod : NG.IsProdLevel (mlX M X i).J :=
    mt_tr M (fun _ _ Mr => NG.IsProdLevel Mr.J) (X.nd.mu_w i).symm hj1 _ _ _ _ (hMI.prod (X.nd.w i) jf)
  have hhyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ B :=
    mt_tr M (fun _ _ Mr => NG.HypOutside Mr.J Mr.χ B) (X.nd.mu_w i).symm hj1 _ _ _ _ (hMI.hyp (X.nd.w i) jf)
  have hbad : ∀ w (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ B :=
    fun w s hw hc => l0 D cf C tp A.pl M big X T Sp i w s hw hc
  have hlin : ∀ w k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (mlX M X i).wt.W),
      NG.tN (mlX M X i).J s ϖ k (c • f + f') = c • NG.tN (mlX M X i).J s ϖ k f + NG.tN (mlX M X i).J s ϖ k f' := by
    intro w k s ϖ hw hc hu c f f'
    have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (mlX M X i).J (mlX M X i).χ B hhyp s ϖ k (hbad w s hw hc) hu
    simp only [NG.tN]
    rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
  let Par := PlE D.host × ℕ × (Σ s : SplitPlace D.host.E, s.v.adicCompletion (maximalRealSubfield D.host.E))
  let Good : Par → Prop := fun p => SplitOut X.nd i p.1 ∧ IsConjPl D.host p.1 p.2.2.1.w ∧
    IsUnif D.host.E p.2.2.1.v p.2.2.2 ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ D.R.nV
  let op : Par → (GAf D.host.E D.R.nV → (mlX M X i).wt.W) → (GAf D.host.E D.R.nV → (mlX M X i).wt.W) :=
    fun p => NG.tN (mlX M X i).J p.2.2.1 p.2.2.2 p.2.1
  let io : X.nd.O i →+* ℂ := ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
    (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))
  let lam : X.nd.X i → Par → ℂ := fun x p => io ((X.nd.hT i p.1 p.2.1 : X.nd.X i → X.nd.O i) x)
  have hdec : ∀ x y, y ∈ (⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) ↔
      ∀ p, Good p → op p ((mlX M X i).real y) = lam x p • (mlX M X i).real y := by
    intro x y
    refine mem_iSup_iff (mlX M X i).real (mlX M X i).real_inj _ hind htop Good op
      (fun p hp => hlin _ _ _ _ hp.1 hp.2.1 hp.2.2.1) (fun P p hp => ?_) (lam x) (fun P => ptV P = some x)
      (fun P => ?_) y
    · exact l1 D (X.nd.mu i) (X.nd.j i) (mlX M X i) B hprod hhyp (F P) (irr P) p.2.2.1 p.2.2.2 p.2.1
        (hbad _ _ hp.1 hp.2.1) hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    · rw [hpt P x]
      constructor
      · rintro h ⟨w, k, s, ϖ⟩ ⟨hw, hc, hu, hk1, hk2⟩ z hz
        exact h w k s ϖ hw hc hu hk1 hk2 z hz
      · intro h w k s ϖ hw hc hu hk1 hk2 z hz
        exact h ⟨w, k, s, ϖ⟩ ⟨hw, hc, hu, hk1, hk2⟩ z hz
  have hinjC : Function.Injective (Sp.iotaC (X.nd.j i) (X.nd.w i)) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := (Sp.phO _ _ i hmem).surjective a
    obtain ⟨b', rfl⟩ := (Sp.phO _ _ i hmem).surjective b
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    have hio : Function.Injective io :=
      (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp ((Sp.iq i).injective.comp
        (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i))))
    rw [hio hab]
  let φ : FractionRing (Sp.B.Oc (X.nd.j i) (X.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK _ _ i hmem).toRingHom =
      (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (X.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    rw [← Sp.iotaC_coh]
  have hφ : ∀ y, φ (Sp.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← Sp.phK_emb _ _ i hmem y, ← Sp.iq_LL i y]
    exact congrArg (fun f : FractionRing (X.nd.O i) →+* ℂ => f (X.nd.embK i y)) hφK
  have hdim : ∀ x, X.nd.mult i x = Module.finrank ℂ
      ↥(⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) := by
    intro x
    rw [l2a D A.pl M C big X T Sp (X.nd.j i) (X.nd.w i) i hmem x]
    refine l2b D M Sp.B (X.nd.j i) (X.nd.w i) (X.nd.mu i) (X.nd.j_range i).1 (X.nd.j_range i).2 (X.nd.mu_w i) φ hφ
      (fun v k => algebraMap _ _ (Sp.phO _ _ i hmem ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x))) _ ?_ ?_ ?_
    · intro v k hvk
      exact GlobalTheory.T.splitEx_every_datum D v hvk.1
    · intro v k s ϖ hvk hc hu c f f'
      exact hlin v k s ϖ ((genAt_iff' Sp i v k).1 hvk).1 hc hu c f f'
    · intro y
      rw [hdec x y]
      constructor
      · intro h v k s ϖ hvk hc hu
        obtain ⟨hv, hk1, hk2⟩ := (genAt_iff' Sp i v k).1 hvk
        have e := h ⟨v, k, s, ϖ⟩ ⟨hv, hc, hu, hk1, hk2⟩
        rw [hφalg, ← Sp.iotaC_coh]
        exact e
      · rintro h ⟨v, k, s, ϖ⟩ ⟨hv, hc, hu, hk1, hk2⟩
        have e := h v k s ϖ ((genAt_iff' Sp i v k).2 ⟨hv, hk1, hk2⟩) hc hu
        rw [hφalg, ← Sp.iotaC_coh] at e
        exact e
  refine ⟨fun x => ?_, hdim⟩
  by_contra hno
  push_neg at hno
  have hbot : (⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) = ⊥ :=
    eq_bot_iff.2 (iSup₂_le fun P hP => absurd hP (hno P))
  have h0 := hdim x
  rw [hbot, finrank_bot] at h0
  have hne0 := X.nd.eig_ne i x
  apply hne0
  have : Module.Finite (FractionRing (X.nd.O i)) (TensorProduct (X.nd.O i) (FractionRing (X.nd.O i)) (X.nd.Mt i)) :=
    inferInstance
  exact Submodule.finrank_eq_zero.1 h0
end GlobalTheory.AutPts
end
