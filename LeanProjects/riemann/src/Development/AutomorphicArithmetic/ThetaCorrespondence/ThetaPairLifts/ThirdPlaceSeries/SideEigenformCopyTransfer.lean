import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Rows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalExOfCgTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepTransportOfCopyAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.HeightCounting.SideCopy.Restage
set_option maxHeartbeats 1000000
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
private theorem eigen_zero_one_transfer (h : CopyAll D D' ι e)
    (hs : ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1) : ∀ i (s : D'.ntw.Sig i) P, D'.ntw.hEig i s 0 P = 1 := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact hs
private theorem lowAll_eq (h : CopyAll D D' ι e) : lowAll D' = lowAll D := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact ((Eq.refl (lowAll D)) :))
private theorem over_S0_transfer (h : CopyAll D D' ι e) (low : Finset ℕ) (hs : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) low)) :
    ∀ i, OverSet D' (D'.ntw.S0 i) (insert (D'.ntw.l i) low) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem hecke_map_transfer (h : CopyAll D D' ι e) (hs : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i →
      IsSplitPl D.host P → k ≤ D.R.r →
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)) :
    ∀ i j b k P (x : D'.ntw.B i j b), 1 ≤ j → j ≤ D'.R.m → P ∉ D'.ntw.S0 i → IsSplitPl D'.host P → k ≤ D'.R.r →
      D'.nexp.embB i j b (D'.ntw.hk i j b k P x) = D'.nexp.hkF i j b k P (D'.nexp.embB i j b x) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem eigen_system_transfer (h : CopyAll D D' ι e)
    (hs : ∀ i (s : D.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (GlobalTheory.EigTie.sigEv s)) :
    ∀ i (s : D'.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D'.nexp i (D'.ntw.jS i s) (D'.ntw.side i s) (GlobalTheory.EigTie.sigEv s) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem emb_eq_of_equiv {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) (i : D.ntw.Tw) (x : ↥(overD D r).LL0) :
    D.ntw.emb0 i (e x) = (overD D r).ntw.emb0 i x ∧ D.ntw.emb0b i (e x) = (overD D r).ntw.emb0b i x :=
  ⟨eq_of_heq (h.emb0 i i HEq.rfl x), eq_of_heq (h.emb0b i i HEq.rfl x)⟩
private theorem hecke_coeff_transfer (h : CopyAll D D' ι e) {c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ}
    {c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ} (hc : SameUnits c c')
    (hs : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
      c i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)) :
    ∀ i b P, P ∉ D'.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D'.host.E D'.nd.Om, IsFrob (F := D'.host.E) (D'.nd.plOm.1 P) (normV P) σ →
      c' i b P = Units.map (algebraMap (D'.ntw.O0 i) (D'.ntw.O i)).toMonoidHom
        (if b then D'.ntw.delta i σ else (D'.ntw.delta i σ)⁻¹) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i b P hP σ hσ
  have h1 := eq_of_heq (hc i i b P P HEq.rfl HEq.rfl)
  have h2 := hs i b P hP σ hσ
  exact (by with_unfolding_all exact ((h1.trans h2) :))
private theorem psi_law_transfer (h : CopyAll D D' ι e) {S : RatDat D.ntw} {S' : RatDat D'.ntw} {θ θ'} (h1 : PsiStd D θ) (h2 : PsiStd D' θ')
    (h3 : PsiLaw D S θ) : PsiLaw D' S' θ' := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hpl : D.naut.plGw = (overD D r).naut.plGw := eq_of_heq h.pl
  have hxi : ∀ kv, NX.xiRed (overD D r) kv = NX.xiRed D kv := fun kv => by
    unfold NX.xiRed NX.pG
    rw [← hpl]
    rfl
  intro i b u hu hu'
  have a1 := h1 ⟨u, hu'⟩
  have a2 := h2 ⟨u, hu'⟩
  simp only [hxi] at a2
  have a3 : e ((psiUOf (overD D r).nd (NX.xiRed (overD D r)) θ' ⟨u, hu'⟩ : (↥(overD D r).LL0)ˣ) : ↥(overD D r).LL0) =
      ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0) := by
    apply (embLL0 D).injective
    rw [h.cp.embLL0_eq, a1]
    simp only [hxi]
    exact (by with_unfolding_all exact (a2 :))
  have a4 := h3 i b u hu hu'
  rw [← a3] at a4
  have a5 : ∀ (i : D.ntw.Tw) x, readLL0 S i b (e x) = readLL0 S' i b x := fun i x => by
    obtain ⟨b1, b2⟩ := emb_eq_of_equiv h.cp i x
    cases b
    · exact (by with_unfolding_all exact ((congrArg (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) b2) :))
    · exact (by with_unfolding_all exact ((congrArg (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) b1) :))
  exact (by with_unfolding_all exact ((a4.trans (a5 i _)) :))
open Formalism.L2.DIV GlobalTheory.HeightCounting.ThetaSt in
private theorem psi_standard_of_units {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) {θ}
    (hl : ∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd)
    (hp : ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) : PsiStd D θ := by
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  rintro ⟨v, hv⟩
  obtain ⟨g, rfl⟩ := eG.surjective v
  let u : P0 := ⟨g, (hl g).2 hv⟩
  have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
  have h1 := hp u hv
  rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum] at h1
  have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), D.what₂.embLL (ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) =
      Complex.exp (2 * Real.pi * Complex.I / (D.host.g kv.1 : ℂ)) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
        (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
    intro kv
    have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
        (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
      rw [map_mul, _root_.GlobalTheory.HeightCounting.ThetaSt.res_xiBar_alt kv (hT.place kv), hT.comp u kv, ThetaSt.supSum_map]
      rfl
    rw [← hres]
    have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
        (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
      apply (res kv).injective
      rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hW kv _ _ hb, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine (congrArg D.what₂.embLL h1).trans ?_
  rw [← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
    map_inv₀, map_prod, Finset.prod_inv_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun kv _ => hfac kv)
private theorem lambda_datum_transfer (h : CopyAll D D' ι e) {cf : CharFrame D} {cf' : CharFrame D'} (hf : SameFrame cf cf')
    (hs : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) :
    ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  obtain ⟨Z, hO, hT, rfl, hq, hF⟩ := hs
  have hmu : Z.C.mu0 = cf'.mu0 := eq_of_heq hf.mu0
  have hd : Z.C.del = cf'.del := eq_of_heq hf.del
  have hd' : Z.C.del' = cf'.del' := eq_of_heq hf.del'
  have hj : D.ntw.jL = (overD D r).ntw.jL := eq_of_heq h.jL
  have hs2 : D.ntw.s2 = (overD D r).ntw.s2 := eq_of_heq h.s2
  have hX : D.ntw.Xv = (overD D r).ntw.Xv := eq_of_heq h.Xv
  let Z' : GlobalTheory.LamTie.LamDat (overD D r) := ⟨cf', Z.q0, Z.w0, Z.c, Z.chi⟩
  have hl : ∀ l a c, Z'.lam0 l a c = Z.lam0 l a c := fun l a c => by
    change cf'.mu0 a * (if l = D.host.pde then cf'.del' else cf'.del) * _ = _
    rw [← hmu, ← hd, ← hd']
    rfl
  refine ⟨Z', ⟨(by with_unfolding_all exact (hO.places :)), (by with_unfolding_all exact (hO.aux :)), (by with_unfolding_all exact (hO.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((h.cp.inW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), j, fun x => ?_, ?_⟩
  · exact (by with_unfolding_all exact (((congrArg j (h.cp.embLL0_eq x).symm).trans ((t1 (e x)).trans
      (congrArg (GlobalTheory.ToricDenom.toBar D.ntw i) (emb_eq_of_equiv h.cp i x).1))) :))
  · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, ← hj, ← hs2, ← hX]
    simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk] at t2
    exact (by with_unfolding_all exact (t2 :))
open GlobalTheory.EigTie GlobalTheory.TwInputs Formalism.MainNotions.IntegralHeckeForms in
private theorem is_eig_sys_sig_ev_of_eig_occ {cf : CharFrame D} {Rw low Pq S hL eig θ} (Bs : SideB D cf Rw low Pq S hL eig θ) {Sb : Finset (PlE D.host)} (hSb : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) (hOcc : EigOcc D S θ hL Sb eig) (i : D.ntw.Tw) (s : D.ntw.Sig i) :
    IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (sigEv s) := by
  classical
  obtain ⟨h1, h2⟩ := D.ntw.jS_range i s
  obtain ⟨hiso, hgood, -⟩ := Bs.rhoS i s
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc _ h1 h2 _ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i (D.ntw.side i s) x hx0
  set e := Bs.eF i (D.ntw.jS i s) (D.ntw.side i s) h1 h2 with he
  have hact : ∀ g : G0g D.nd, e (D.nexp.actG i _ _ g (e.symm (Φ x))) = Φ (actL D S (D.ntw.jS i s) g x) := fun g => by
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    have hc : ((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A (D.ntw.jS i s)).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  have hE : eG D.nexp i _ _ (e.symm (Φ x)) = e.symm (Φ x) := by
    letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [hact]
    rfl
  have hU : e.symm (Φ x) ∈ Fm0 D.nexp i (D.ntw.jS i s) (D.ntw.side i s) := by
    simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    rintro ⟨u, hu⟩
    have hu' : u ∈ Formalism.IndefR.NX.U D.nd := by
      have := hu
      rw [Bs.exp.U_eq] at this
      exact this
    have hx2 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hxg).2 ⟨u, hu'⟩)
    apply e.injective
    rw [map_smul, e.apply_symm_apply, Bs.psiU i _ u hu hu']
    refine (hact u).trans ?_
    rw [hx2, hΦs]
    rfl
  refine ⟨e.symm (Φ x), ⟨_, hU, hE⟩, by simpa using hΦ0, ?_⟩
  rintro k P ⟨hk1, hk2, hsp, hP⟩
  apply e.injective
  rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply, sigEv,
    Bs.rowS_eig i s k P hk1 hk2 hsp hP]
  have h3 := hΦT (hL (D.ntw.jS i s) k P) (Bs.hs _ h1 h2 k P) x
  rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
  rw [mul_smul]
  congr 1
  exact h3.symm
theorem side_data_transferred_alt (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (h : CopyAll D D' ι e) {cf : CharFrame D} {cf' : CharFrame D'}
    (hf : SameFrame cf cf') (hCS : CharSide D cf) {Rw Pq S hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ)
    {jE'} (A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D' cf' jE') (hRC : RowCusp D Rw) (hG : GalEx D') (hCh : GlobalTheory.RowTie.ChebSplit D'.nd)
    {S' : RatDat D'.ntw} (In : RatIn D' S') (hSb : OverSet D' In.Sb (lowAll D')) {Sb Sb'}
    (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (hT' : GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' In.eig)
    (hE : ∀ i (s : D.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (GlobalTheory.EigTie.sigEv s))
    (hψ : PsiStd D θ) (hψ' : PsiStd D' In.θ) {Pq'}
    (c : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ) (hc : SameUnits B.cHk c) (X : NExpTied D')
    (pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (hadm : NX.AdmTw D' i k Q ψ),
      (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D' Pq' Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D' Pq' (D'.ntw.pD i))
    (eF : ∀ i j b, 1 ≤ j → j ≤ D'.R.m → D'.nexp.Fm i j b ≃ₗ[FractionRing (D'.ntw.O i)] Fm S' i j b)
    (bsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i j b),
      x ∈ D'.nexp.Bsup i j b ↔ eF i j b h1 h2 x ∈ Bsup S' i j b)
    (act : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i j b),
      eF i j b h1 h2 (D'.nexp.actG i j b g x) = actG S' i j b (In.rho j h1 h2) (In.chi j h1 h2) g (eF i j b h1 h2 x))
    (hkEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (k : ℕ) (P : PlE D'.host) (x : D'.nexp.Fm i j b), P ∉ D'.ntw.S0 i →
      IsSplitPl D'.host P → k ≤ D'.R.r → eF i j b h1 h2 (D'.nexp.hkF i j b k P x) =
        algebraMap (D'.ntw.O i) (FractionRing (D'.ntw.O i)) (c i b P) ^ k •
          hkF D' S' i j b (In.hL j) (In.hs j h1 h2) k P (eF i j b h1 h2 x)) :
    ∃ B' : SideB D' cf' A'.row (lowAll D') Pq' S' In.hL In.eig In.θ, B'.exp = X ∧ B'.eF = eF ∧ ∀ i, In.Sb ⊆ D'.ntw.S0 i := by
  obtain ⟨Rp⟩ : Nonempty (RingPart D' cf' (lowAll D')) := by
    rw [lowAll_eq h]
    exact UpperTheory.nonempty_coefficientRingData_of_isomorphic_CMDatum h hf A'.bare _ (RingPart.of B)
  have hS : ∀ i, In.Sb ⊆ D'.ntw.S0 i := hSb.subset_twistExceptionalPlaces subset_rfl Rp.tw
  have hP : PsiLaw D' S' In.θ := psi_law_transfer h hψ hψ' B.psiU
  have hrow := fun i (s : D'.ntw.Sig i) => UpperTheory.heckeEigenspace_descent_of_equivariant_equiv D' S' In X.U_eq hP hS c eF act hkEq i _ _ (D'.ntw.jS_range i s).1
    (D'.ntw.jS_range i s).2 _ (eigen_system_transfer h hE i s)
  choose rowS r1 r2 r3 using hrow
  have hρ : RhoSpec D' A'.row rowS := _root_.UpperTheory.galoisRep_transport_of_copyAll_alt hArt h hf hCS Rw jE' A' hRC hG hCh Sb Sb' eig In.eig hT hT' S S' B.cHk c hc
    B.rowS rowS B.rowS_eig r3 B.rhoS fun i s => ⟨r1 i s, r2 i s⟩
  exact ⟨{ twF := Rp.twF, tw := Rp.tw, cover := UpperTheory.sidePlace_exists_of_copyAll h B.cover, chiD := Rp.chiD, chi := Rp.chi, eta_eq := Rp.eta_eq
           ringSpec_normalisedCharacter_eq := Rp.ringSpec_normalisedCharacter_eq, del_eq := Rp.del_eq, iCq_embO := Rp.iCq_embO, embO_star := Rp.embO_star
           deltaRead := Rp.deltaRead, exp := X, pq := pq, psiU := hP, rho := In.rho, chiL := In.chi, hs := In.hs, eF := eF
           bsup := bsup, act := act, cHk := c, hkEq := hkEq, cHk_del := hecke_coeff_transfer h hc B.cHk_del, hk_emb := hecke_map_transfer h B.hk_emb
           sigSpan := sigSpan_copy h B.sigSpan, rowS := rowS, rowS_eig := r3, hEig_zero := eigen_zero_one_transfer h B.hEig_zero, rhoS := hρ },
    rfl, rfl, hS⟩
private theorem exists_full_equiv {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : GlobalTheory.HeightCounting.Up.CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩
end GlobalTheory.HeightCounting.SideCopy.Restage
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.SideCopy.Restage
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
private theorem frame_components_heq_alt {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
section State
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
private theorem same_frame_of_eq {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {P' : Pre2 K w'}
    (hB : B'.toPre = B.toPre) (hf : HEq f' f) (x : St P) (x' : St P') : SameFrame (cfOf x) (cfOf x') := by
  have h : HEq w'.I.C w.I.C := (heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm)
  obtain ⟨h1, h2, h3, h4⟩ := frame_components_heq_alt hB h
  exact ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩
theorem psi_std_of_level_i {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) : PsiStd (Dof x) l.rat.In.θ :=
  psi_standard_of_units x.m.z.pins.keep.psi l.rat.rat.lvl l.rat.rat.psi
theorem eig_true_and_eig_occ_of_low {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) {Sb : Finset (PlE (Dof x).host)} (h1 : l.rat.In.Sb ⊆ Sb)
    (h2 : GlobalTheory.TwInputs.Eig.Low (Dof x) Sb) : GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb l.rat.In.eig ∧
      GlobalTheory.TwInputs.EigOcc (Dof x) l.rat.S l.rat.In.θ l.rat.In.hL Sb l.rat.In.eig := by
  have h := _root_.GlobalTheory.TwInputs.Eig.eig_of_rational_adjoint hL x.r.Y x.m.z.pins.char.base.lev x.m.intersectionNumber_baseChange.prim.unif x.m.z.pins.char.base.models.HW
    x.m.z.good.2 l.rat.rat l.a.A.wdT l.a.A.row l.a.row h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨(congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb l.rat.In.eig) hC).mp h.1, h.2⟩
end State
private theorem eig_low_s0 (D : D7) {F : TwFrameC D} (T : TwistFrameLowIndexCompatibility D F (lowAll D)) (i : D.ntw.Tw) :
    GlobalTheory.TwInputs.Eig.Low D (D.ntw.S0 i) := by
  refine (GlobalTheory.TwInputs.Eig.low_SbD D).mono (OverSet.subset_twistExceptionalPlaces (fun P hP => ?_) subset_rfl T i)
  obtain ⟨p, h1, -, h3⟩ := (RatSide.lowSet_finite D).mem_toFinset.1 hP
  exact ⟨p, h1, h3⟩
end GlobalTheory.HeightCounting.SideCopy.Restage
open GlobalTheory.HeightCounting.SideCopy GlobalTheory.HeightCounting.SideCopy.Restage in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.side_eigenform_copy_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∀ X : NExpTied (Dof x''), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) → ∀ eF : (∀ i j b, 1 ≤ j → j ≤ (Dof x'').R.m → (Dof x'').nexp.Fm i j b ≃ₗ[FractionRing ((Dof x'').ntw.O i)] Fm l''.rat.S i j b), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (y : (Dof x'').nexp.Fm i j b), y ∈ (Dof x'').nexp.Bsup i j b ↔ eF i j b h1 h2 y ∈ Bsup l''.rat.S i j b) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (g : G0g (Dof x'').nd) (y : (Dof x'').nexp.Fm i j b), eF i j b h1 h2 ((Dof x'').nexp.actG i j b g y) = actG l''.rat.S i j b (l''.rat.In.rho j h1 h2) (l''.rat.In.chi j h1 h2) g (eF i j b h1 h2 y)) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (eF i j b h1 h2 y)) → ∃ b0 : _root_.GlobalTheory.HeightCounting.SettingsFormsData l''.a l''.rat l''.Pq, b0.Bs.exp = X ∧ b0.Bs.eF = eF := by
  intro hPr _ hL K B' f' T' w' _ _ _ B f T w hE hf _ _ _ _ _ P x lb P' _ x' _ hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _
    cHk hc X hpq eF hsup hact hecke_map_transfer
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := exists_full_equiv hN hG.pl hD
  have hF : SameFrame (cfOf x) (cfOf x'') := same_frame_of_eq hE.1 hf x x''
  obtain ⟨Sb, a1, a2, a3⟩ := GlobalTheory.TwInputs.Eig.exists_low lb.rat.In.Sb (Dof x).ntw.S0 lb.b.Sb_le (eig_low_s0 _ lb.b.Bs.tw)
  obtain ⟨Sb', b1, b2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) l''.rat.In.Sb (fun i => i.elim) (fun i => i.elim)
    fun i => i.elim
  obtain ⟨hT, hO⟩ := _root_.GlobalTheory.HeightCounting.SideCopy.Restage.eig_true_and_eig_occ_of_low lb.toLI a1 a2
  obtain ⟨B2, h1, h2, h3⟩ := _root_.GlobalTheory.HeightCounting.SideCopy.Restage.side_data_transferred_alt hPr.what₂.art h hF lb.a.A.chr lb.b.Bs l''.a.A lb.cusp
    (_root_.GlobalTheory.HeightCounting.galEx_of_cgTrue_alt hL hPr.what₂.fin hPr.what₂.gal _ l''.a.A.wdT ⟨l''.a.cg⟩) (GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb _)
    l''.rat.In l''.rat.rat.Sb_le hT (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.eig_true_and_eig_occ_of_low l'' b1 b2).1 (is_eig_sys_sig_ev_of_eig_occ lb.b.Bs a3 lb.rat.In.ks hO)
    (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.psi_std_of_level_i lb.toLI) (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.psi_std_of_level_i l'') cHk hc X hpq eF hsup hact hecke_map_transfer
  refine ⟨⟨B2, h3, ?_, lambda_datum_transfer h hF lb.b.lam⟩, h1, h2⟩
  rw [lowAll_eq h]
  exact over_S0_transfer h _ lb.b.rootsOfUnityRing_le_wittIntegers
end
end
