import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOutsideNonHyperspecialOfLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicHeckeOperatorHyperspecialActsByScalarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeMultiplicityEqFinrankJointEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplexStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutPts

theorem l0 : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation
theorem l1 : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := GlobalTheory.T.isotypic_heckeOperator_hyperspecial_acts_by_scalar
theorem l2a : ∀ (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ) (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i), X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)) (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := GlobalTheory.T.heckeMultiplicity_eq_finrank_jointEigenspace
theorem l2b : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := GlobalTheory.T.finrank_jointEigenspace_coefficientField_complex

theorem mt_tr {D : D7} (M : MtFam D) (Pr : ∀ (μ : D.what₂.Tup) (j : ℕ), MtReal D μ j → Prop) {μ μ' : D.what₂.Tup}
    {j j' : ℕ} (hμ : μ = μ') (hj : j = j') (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) :
    Pr μ j (M μ j a1 a2) → Pr μ' j' (M μ' j' b1 b2) := by
  subst hμ hj; exact id

theorem genAt_iff' {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    {X : LocNd (lay0 D)} {T : LocTw X} (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.what₂.places.resChar (X.nd.w i)) (Sp.B.Qc (X.nd.j i) (X.nd.w i)) v k ↔
      (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have h : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hl : X.nd.l i = D.what₂.places.resChar (X.nd.w i) := (X.nd.w_l i).symm
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar (X.nd.w i)) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, Sp.Q_eq _ _ i h, hl]
  tauto

theorem mem_iSup_iff {V Wf : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Wf] [Module ℂ Wf] {ι : Type}
    [Finite ι] (real : V →ₗ[ℂ] Wf) (hreal : Function.Injective real) (typ : ι → Submodule ℂ V)
    (hind : iSupIndep typ) (htop : ⨆ P, typ P = ⊤) {Par : Type} (Good : Par → Prop) (op : Par → Wf → Wf)
    (hlin : ∀ p, Good p → ∀ (c : ℂ) (f f' : Wf), op p (c • f + f') = c • op p f + op p f')
    (hsc : ∀ P p, Good p → ∃ c : ℂ, ∀ y ∈ typ P, op p (real y) = c • real y) (lam : Par → ℂ) (Q : ι → Prop)
    (hQ : ∀ P, Q P ↔ ∀ p, Good p → ∀ y ∈ typ P, op p (real y) = lam p • real y) (y : V) :
    y ∈ (⨆ P ∈ {P | Q P}, typ P) ↔ ∀ p, Good p → op p (real y) = lam p • real y := by
  classical
  have hop0 : ∀ p, Good p → op p 0 = 0 := fun p hp => by
    have h := hlin p hp 1 0 0
    rw [one_smul, add_zero, one_smul] at h
    exact (add_eq_left.1 h.symm)
  have hopadd : ∀ p, Good p → ∀ f f' : Wf, op p (f + f') = op p f + op p f' := fun p hp f f' => by
    simpa using hlin p hp 1 f f'
  have hopsmul : ∀ p, Good p → ∀ (c : ℂ) (f : Wf), op p (c • f) = c • op p f := fun p hp c f => by
    simpa [hop0 p hp] using hlin p hp c f 0
  let Es : Submodule ℂ V :=
    { carrier := {y | ∀ p, Good p → op p (real y) = lam p • real y}
      zero_mem' := fun p hp => by simp [hop0 p hp]
      add_mem' := fun {a b} ha hb p hp => by
        simp only [map_add, hopadd p hp, ha p hp, hb p hp, smul_add]
      smul_mem' := fun c a ha p hp => by
        simp only [map_smul, hopsmul p hp, ha p hp, smul_comm c (lam p)] }
  show y ∈ _ ↔ y ∈ Es
  constructor
  · intro hy
    refine (iSup₂_le fun P hP => ?_ : (⨆ P ∈ {P | Q P}, typ P) ≤ Es) hy
    intro z hz p hp
    exact (hQ P).1 hP p hp z hz
  · intro hy
    have hy' : y ∈ ⨆ P, typ P := by rw [htop]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp typ y).1 hy'
    rw [← hsum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun P hPs => ?_
    by_cases h0 : f P = 0
    · rw [h0]; exact Submodule.zero_mem _
    refine (le_iSup₂ (f := fun P (_ : P ∈ {P | Q P}) => typ P) P ?_) (hf P)
    show Q P
    refine (hQ P).2 fun p hp => ?_
    obtain ⟨c, hc⟩ := hsc P p hp
    choose cc hcc using fun P' => hsc P' p hp

    have hz : ∑ P' ∈ f.support, (cc P' - lam p) • f P' = 0 := by
      apply hreal
      rw [map_zero, map_sum]
      have e1 : ∀ P' ∈ f.support, real ((cc P' - lam p) • f P') = op p (real (f P')) - lam p • real (f P') := by
        intro P' _
        rw [map_smul, hcc P' _ (hf P'), sub_smul]
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have e2 : ∀ s : Finset ι, op p (real (∑ P' ∈ s, f P')) = ∑ P' ∈ s, op p (real (f P')) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hop0 p hp]
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, hopadd p hp, ih]
      have e3 : (∑ P' ∈ f.support, f P') = y := hsum
      have e4 : ∑ P' ∈ f.support, op p (real (f P')) = op p (real y) := by rw [← e2, e3]
      have e5 : ∑ P' ∈ f.support, real (f P') = real y := by rw [← e3, map_sum]
      rw [e4, e5, hy p hp, sub_self]
    have hz' := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero typ).1 hind) f.support
      (fun P' => (cc P' - lam p) • f P') (fun P' _ => Submodule.smul_mem _ _ (hf P')) hz P
      (Finsupp.mem_support_iff.2 h0)
    have hcl : cc P = lam p := by
      rcases smul_eq_zero.1 hz' with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h h0
    intro z hz
    rw [hcc P z hz, hcl]

end GlobalTheory.AutPts

namespace GlobalTheory.AutPts

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem pts : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → (∀ x, ∃ P, ptV P = some x) ∧ ∀ x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV P = some x}, ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) := by
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
