import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOfEigenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphicPointsExistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisFamilyIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckePolMapEqFrobPolStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMuUnrFrobStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MEmbSph
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsResidueFieldMapStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMuCStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.AutPart.exists_autSpec_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp
  classical
  choose ι hfin F hF using fun i : X.nd.Loc => GlobalTheory.T.algebraicModularForms_irreducible_decomposition D (X.nd.mu i) (X.nd.j i) (mlX M X i)
  have irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (F i P) := fun i => (hF i).1
  have hinj := fun i => (hF i).2.1
  have hsurj := fun i => (hF i).2.2.1
  have hne := fun i => (hF i).2.2.2.1
  have hind := fun i => (hF i).2.2.2.2.1
  have htop := fun i => (hF i).2.2.2.2.2
  obtain ⟨ptV, hptV⟩ : ∃ ptV : ∀ i, ι i → Option (X.nd.X i), ∀ i P x, ptV i P = some x ↔
      (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) := by
    refine ⟨fun i P => if h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) then some h.choose else none, fun i P x => ?_⟩
    dsimp only
    by_cases h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)
    · rw [dif_pos h]
      constructor
      · rintro ⟨⟩; exact h.choose_spec
      · intro hx
        rw [_root_.GlobalTheory.T.galois_family_local_condition_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i _ (hne i P) _ _ h.choose_spec hx]
    · rw [dif_neg h]
      exact ⟨fun h' => absurd h' (by simp), fun hx => (h ⟨x, hx⟩).elim⟩
  have hpts := fun i => haveI := hfin i; _root_.GlobalTheory.T.galois_family_unramified_outside_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i)
  choose μ hμc hμ using _root_.GlobalTheory.T.galois_family_crystalline_weights_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose κ hκ using _root_.GlobalTheory.T.galois_family_determinant_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose b hb using fun i : X.nd.Loc => GlobalTheory.algWt_contragredient D.host.E D.R.nV (mlX M X i).wt
  have hralg : ∀ {a} (π : D.naut.CG a) τ, D.naut.ralg π → ∀ z ∈ D.naut.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
    fun π τ h => ((D.naut.ralg_def π).1 h τ).2
  refine ⟨{
    iotaQ := Sp.iq
    iotaQC := fun i => (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)))
    iota_LL := Sp.iq_LL
    iotaQ_alg := Sp.iq_alg
    muC := μ
    muC_csd := hμc
    AV := ι
    finAV := hfin
    ptV := ptV
    typeV := fun i P => ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real)
    typeV_ne := hne
    typeV_indep := hind
    typeV_top := htop
    pt_surj := fun i => (hpts i).1
    eig_dim := fun i => (hpts i).2
    locV := fun i P w => D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    satV := fun i P w => D.nbc.satAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    locV_unr := fun i P w => haveI := hfin i; _root_.GlobalTheory.T.galois_family_irreducible_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w
    pt_loc := fun i P x hx w hw => haveI := hfin i; _root_.GlobalTheory.T.galois_family_trace_frobenius_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i) P x hx w hw
    infWt := fun i => D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
    locW := fun i σ w => A.row.locR σ w
    satW := fun i σ w => A.row.satR σ w
    lab_loc := fun i k σ v => A.row.lab_eq k σ v
    wdOf := fun i {a} r w => A.wd.wdOf (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_dim := fun i {a} r w => A.wd.wdOf_dim (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_unr := fun i {a} r w => A.wd.wdOf_unr (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_frob := fun i {a} r w => A.wd.wdOf_frob (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_ine := fun i {a} r w => A.wd.wdOf_ine (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0 := fun i {a} r w => A.wd.wdOf_mono0 (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsCrysW := fun i {a} r w => A.wd.IsCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsPotCrysW := fun i {a} r w => A.wd.IsPotCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsdRW := fun i {a} r w => A.wd.IsdRW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsW := fun i {a} r τ => A.wd.jumpsW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r τ
    wdOf_unrL := fun i {a} r w => A.wd.wdOf_unrL (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0L := fun i {a} r w => A.wd.wdOf_mono0L (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsInf := fun i {a} π τ => (D.naut.infG π ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf a)
    locAutHodgeTateWeightsLevelZero := fun i τ => (D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
      ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf D.R.nV)
    jumpsInf_def := fun i {a} π τ h => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec a z (hralg π _ h z hz)
    locAut_hodgeTateWeightsLevelZero_def := fun i τ => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec _ z ((D.nbc.infW_alg _ _ _).2 z hz)
    chi_mu := fun i w hw => _root_.GlobalTheory.T.galois_family_hecke_compatible_alt hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i (μ i) (hμc i) (hμ i) w hw
    kFbar := κ }, {
    embAV := fun i P => (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P })
    embAV_inj := fun i P P' h => hinj i P P' ((A.au.iso _ _ _ _ _).1 h).2
    embAV_loc := fun _ _ _ => rfl
    embAV_sat := fun _ _ _ => rfl
    embAV_sph := fun i P w hw => haveI := hfin i; _root_.GlobalTheory.SphNonSplit.sphAU_of_not_split_m_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w hw
    embAV_inf := fun i P => by
      exact (congrArg (D.nbc.infW (X.nd.j i)) (A.au.wt _ _ _ _ (b i) (hb i).1)).symm }, ⟨{
    iotaQ := fun _ => rfl
    iotaQC := fun _ => rfl
    kFbar := hκ
    locW := fun _ _ _ => rfl
    satW := fun _ _ _ => rfl
    wdOf := fun _ _ _ _ => ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩
    muC := hμ
    S := F
    irr := irr
    inj := hinj
    surj := hsurj
    typeV := fun _ _ => rfl
    ptV := hptV
    emb := fun _ _ => rfl }⟩⟩
end
