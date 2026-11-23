import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsPullOfIsSmulPt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

noncomputable section

namespace GlobalTheory.LetterBasis

section Points

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusExt GlobalTheory.FormalPoint GlobalTheory.TorusModel GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.GrpTangent GlobalTheory.LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}

theorem isPull_comp {k : T' ⟶ T} {k' : T'' ⟶ T'} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull k.left g g') (h' : GtPt.IsPull k'.left g' g'') : GtPt.IsPull (k' ≫ k).left g g'' := by
  obtain ⟨b', v'⟩ := (isPull_iff _ _ _).1 h'
  refine (isPull_iff _ _ _).2 ⟨by rw [b', ((isPull_iff _ _ _).1 h).1, Category.assoc], fun χ y J hJ => ?_⟩
  exact (v' χ y J hJ).trans ((val_corr hJ (h.2 χ) _).trans (val_pull hJ _ _ _))

theorem eq_of_idem {g g' : GtPt D T} (h : g.IsAdd g g) (h' : g'.IsAdd g' g') : g = g' := by
  have key : ∀ {g : GtPt D T}, g.IsAdd g g → g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 := fun {g} h => by
    obtain ⟨b, v⟩ := (TorusModel.isAdd_iff _ _ _).1 h
    have hb : g.b = 1 := mul_eq_left.1 b.symm
    refine ⟨hb, fun χ y J hJ => ?_⟩
    have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have e := v χ y J hJ
    have e₁ : th D y J (cP D _ χ) g.b g.b = 1 := by rw [hb, C.s01, C.face]
    rw [e₁, _root_.mul_one] at e
    exact mul_eq_left.1 e.symm
  exact pt_ext ((key h).1.trans (key h').1.symm) fun χ y J hJ => ((key h).2 χ y J hJ).trans ((key h').2 χ y J hJ).symm

theorem eq_of_origin (hG : GlobalFnsSt) {g g' : GtPt D D.P.A} (hb : g.b = g'.b) {o : GtPt D (𝟙_ _)}
    (h : GtPt.IsPull (1 : 𝟙_ _ ⟶ D.P.A).left g o) (h' : GtPt.IsPull (1 : 𝟙_ _ ⟶ D.P.A).left g' o) : g = g' :=
  pt_ext hb fun χ y J hJ => gen_unique' D.P.isLB (fun _ _ _ => by rw [hb]) D.P.A.hom (1 : 𝟙_ _ ⟶ D.P.A).left
    (Over.w (1 : 𝟙_ _ ⟶ D.P.A)) (hG _ _ D.P.isAb).2 (g.isGen χ) (g'.isGen χ)
    (fun z I hI => (((isPull_iff _ _ _).1 h).2 χ z I hI).symm.trans (((isPull_iff _ _ _).1 h').2 χ z I hI)) _ _ y J hJ

variable {n : ℕ} {s : ∀ T : Over (Sp R), (T ⟶ D.P.A) → GtPt D T}

theorem smulPt_split (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (hs : IsSplit D n s) (a : O) (b : T ⟶ D.P.A) : smulPt hG oa a (s T b) = s T (b ≫ oa.onB.act a) := by
  have := oa.onB.hom a
  have id₁ : ∀ T, (s T 1).IsAdd (s T 1) (s T 1) := fun T => by simpa using hs.2.1 T 1 1
  have u : smulPt hG oa a (s _ (𝟙 _)) = s _ (oa.onB.act a) := by
    refine eq_of_origin hG ?_ (o := s _ 1) ?_ ?_
    · rw [smulPt_b, hs.1, hs.1, MonObj.pow_comp, Category.id_comp]
    · have e := smulPt_pull hG oa a (1 : 𝟙_ _ ⟶ D.P.A) (hs.2.2 _ _ (1 : 𝟙_ _ ⟶ D.P.A) (𝟙 _))
      rw [Category.comp_id] at e
      rwa [eq_of_idem (smulPt_add hG oa a (id₁ _)) (id₁ _)] at e
    · have e := hs.2.2 _ _ (1 : 𝟙_ _ ⟶ D.P.A) (oa.onB.act a)
      rwa [MonObj.one_comp] at e
  have e := smulPt_pull hG oa a b (hs.2.2 _ _ b (𝟙 _))
  rw [u, Category.comp_id] at e
  exact isPull_unique e (hs.2.2 _ _ b _)

theorem isPull_smulPt_split (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (hs : IsSplit D n s) (a : O) (t r : R) {w : epsR R ⟶ D.P.A} (hw : w ≫ oa.onB.act a = epsScale r ≫ w)
    {ν : GtPt D (epsR R)} (hν : GtPt.IsPull (epsScale t).left (s _ w) ν) :
    GtPt.IsPull (epsScale r).left ν (smulPt hG oa a ν) := by
  have e := smulPt_pull hG oa a (epsScale t) hν
  rw [smulPt_split hG oa hs, hw] at e
  have e₁ := isPull_comp (hs.2.2 _ _ (epsScale r) w) e
  obtain ⟨g, hg⟩ := ConstLie.exists_isPull (epsScale r) ν
  have e₂ := isPull_comp hν hg
  have c : epsScale r ≫ epsScale t = epsScale t ≫ epsScale r := by
    simpa only [Category.comp_id] using (epsScale_mul_assoc r t (𝟙 _)).trans
      ((congrArg (fun q => epsScale q ≫ 𝟙 _) (_root_.mul_comm r t)).trans (epsScale_mul_assoc t r (𝟙 _)).symm)
  rw [c] at e₂
  rwa [isPull_unique e₁ e₂]

theorem b_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) : ν.b = prodPts cf fun i => (e i).b := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  refine (Chart.isLieComb_iff _ _ _).1 ⟨fun i => (u i).b, fun i => (hu i).1, ?_⟩
  have key : ∀ (m : ℕ) (u : Fin m → (epsR R ⟶ D.P.A)) (p : Fin (m + 1) → (epsR R ⟶ D.P.A)),
      (∀ i : Fin m, p i.succ = p i.castSucc * u i) → p (Fin.last m) = p 0 * (List.ofFn u).prod := fun m => by
    induction m with
    | zero => intro u p _; simp
    | succ m ih =>
      intro u p h
      have e := ih (fun i => u i.succ) (fun i => p i.succ) (fun i => h i.succ)
      rw [List.ofFn_succ, List.prod_cons, ← _root_.mul_assoc]
      exact e.trans (congrArg (· * _) (h 0))
  have e := key m (fun i => (u i).b) (fun i => (p i).b) fun i => (ha i).1
  have e₀ : (p 0).b = 1 := h₀.1
  simpa only [e₀, _root_.one_mul] using e

theorem dlog_eq_zero {K : Type} [Field K] {D : DegPre K} {ν : GtPt D (epsR K)} (ht : GtTanR ν) (h : ν.IsZero)
    {φ : D.X → K} (hφ : ∀ x, DlogTan ν x (φ x)) (x : D.X) : φ x = 0 := by
  have := ConstTan.isLocalRing_dual K
  obtain ⟨I, hI⟩ := ConstFam.exists_good' D.P.isLB (cpt (DualNumber K))
  have e := TorusType.val_tangent ht h.1 hφ x (RingHom.id _) _ hI
  rw [(val_corr hI (h.2 x) _).trans (val_one _)] at e
  have e' := toStkA_injective ((map_one _).trans e)
  simpa using (congrArg TrivSqZeroExt.snd e').symm

end Points

theorem existsUnique_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ} {u u' : Fin n → V}
    (hu : LinearIndependent K u) (h : ∀ k, ∃ cf : Fin n → K, u k = ∑ j, cf j • u' j) {w : V}
    (hw : ∃ cf : Fin n → K, w = ∑ j, cf j • u' j) : ∃! cf : Fin n → K, w = ∑ k, cf k • u k := by
  have mem : ∀ {x : V} {u : Fin n → V}, x ∈ Submodule.span K (Set.range u) ↔ ∃ cf : Fin n → K, x = ∑ j, cf j • u j :=
    fun {x u} => (Submodule.mem_span_range_iff_exists_fun K).trans (exists_congr fun _ => eq_comm)
  have := FiniteDimensional.span_of_finite K (Set.finite_range u')
  have e : Submodule.span K (Set.range u) = Submodule.span K (Set.range u') :=
    Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 (Set.range_subset_iff.2 fun k => mem.2 (h k)))
      ((finrank_range_le_card u').trans (finrank_span_eq_card hu).ge)
  obtain ⟨cf, hcf⟩ := mem.1 (e ▸ mem.2 hw)
  exact ⟨cf, hcf, fun cf' h' => funext (Fintype.linearIndependent_iffₛ.1 hu _ _ (h'.symm.trans hcf))⟩

section ThetaShiftProofs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Matrix GlobalTheory.LieEigen GlobalTheory.ConstBasis GlobalTheory.Serre
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

section Ring

variable {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A}
  {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ) (hG : Out.GlobalFnsSt)

theorem eig_of_isPull {ν : Out.GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E)
    (r : A) (p : letI := H.starRing;
      Out.GtPt.IsPull (GrpTangent.epsScale r).left ν (TorusModel.smulPt hG a.oa x ν)) :
    (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) r)) ≫ v.left := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := ConstLie.exists_tr W hG hv
  have hν' := TorusModel.isSmulPt_smulPt hG a.oa x ν
  generalize TorusModel.smulPt hG a.oa x ν = ν' at p hν'
  obtain ⟨g', hg'⟩ := ConstLie.exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (ConstLie.cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := ConstLie.Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  let k : epsR (PowerSeries A) ⟶ epsR (PowerSeries A) :=
    Over.homMk (spMap (epsScaleR (PowerSeries.C (R := A) r))) (LieCombBaseChange.epsScale_over _)
  have p' := ConstLie.Tr.cancel W.spec.1 W.e.surjective hg
    (TorusType.tr_comp (T₁ := epsR A) hg' (GrpTangent.epsScale r) p) k
    (LieCombBaseChange.dualMap_epsScale _ _).symm
  exact congrArg (fun q => q.left) ((ConstLie.main hG E H Dw l Xo c O β Y A b a χ W ν').1.unique
    (ConstLie.lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)) (ConstLie.lieImg_of_tr W hg' (hp.pull k p')))

include hG in

theorem isZero_of_lieImg {ν : Out.GtPt a.D₀ (epsR A)} (h : LieImg W ν 1) : ν.IsZero := by
  obtain ⟨o, ho⟩ := ConstLie.exists_gtComb (D := a.D₀) (m := 0) Fin.elim0 Fin.elim0
  have h₀ := (ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y A b a χ W 0 _ _ o Fin.elim0 1
    (fun j => j.elim0) ho).2 ⟨Fin.elim0, fun j => j.elim0, by simp⟩
  obtain rfl : ν = o := ConstLie.eq_of_red W hG h h₀ rfl
  obtain ⟨_, p, _, h0, _, h⟩ := ho
  exact h ▸ h0

end Ring

variable {K : Type} [Field K] [Algebra c.F K] {a : ArcIn Dw l (RingHom.id c.F) K (algebraMap c.F K)}
  {χ : Sp (PowerSeries K) ⟶ Y.X} (W : Wit Y (a.restrict β) χ)

theorem lieMult_arc (F : Type) [Field F] [IsAlgClosed F] [Algebra K F] [Algebra (FractionRing K) F]
    [IsScalarTower K (FractionRing K) F] (τ : E →+* ℂ) :
    LieMult W.t.act (spMap ((algebraMap K F).comp PowerSeries.constantCoeff))
      (((algebraMap K F).comp (algebraMap c.F K)).comp (embK c τ)) (Dw.mult τ) := by
  classical
  let := H.starRing
  let j := (algebraMap K F).comp (algebraMap c.F K)
  have hinj : Function.Injective fun τ : E →+* ℂ => embK c τ := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective (RingHom.ext fun a =>
      (embK_coe c τ a).symm.trans ((congrArg _ (RingHom.congr_fun h a)).trans (embK_coe c τ' a)))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => j.comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E ℂ) j (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨n, hn, hs⟩ := (a.geom F ⟨_, HostModel.sqrtNegDisc_mem_coeffField c⟩ ⟨_, HostModel.zeta_A_mem_coeff c⟩ rfl rfl
    (algebraMap K F) (IsScalarTower.algebraMap_eq _ _ _)).1 (j.comp (embK c τ))
  have hc : j.comp (embK c τ) H.rt = algebraMap K F (algebraMap c.F K ⟨_, HostModel.sqrtNegDisc_mem_coeffField c⟩) ↔
      τ (H.rt : E) = H.rt0 :=
    j.injective.eq_iff.trans (Subtype.ext_iff.trans (by rw [embK_coe c]))
  have hm : Dw.mult τ = n + Module.finrank (𝓞 E) W.P.D.toPre.X := by
    rw [← W.e.finrank_eq, Datum.mult]
    exact (if_congr hc.symm rfl rfl).trans hs.symm
  rw [hm]
  refine lieMult_level W.P.U.toUnifPre W.P.lin _ (fun x hx => ?_) hσ τ
    (j.injective.comp ((embF c τ).injective.comp RingOfIntegers.coe_injective)) ?_
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    simp
  · refine (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct a.oa.onB.toRingAct) _ W.spec.1 W.spec.2.2.2.1 F _ _ _).2 ?_
    convert hn using 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext x
    simp

theorem arcLieBasis_of_indep (hG : Out.GlobalFnsSt) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K))
    (ht : ∀ τ k, GtTanR (e τ k))
    (he : ∀ τ k v, LieImg W (e τ k) v → ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left =
      spMap (epsScaleR (PowerSeries.C (R := K) (algebraMap c.F K (embK c τ x)))) ≫ v.left)
    (hi : ∀ τ, ∃ k₀, ¬ (e τ k₀).IsZero ∧ ∀ cf, prodPts cf (fun k => (e τ k).b) = 1 → ∀ k, k ≠ k₀ → cf k = 0) :
    ArcLieBasis W e := by
  obtain ⟨g, e₀, v, M, hev, hv, hu, hM⟩ := ConstLie.exists_const_basis hG E H Dw l Xo c O β Y K _ _ χ W
  have lin := ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y K _ _ χ W
  have := W.t.semi.smooth
  let F := AlgebraicClosure (FractionRing K)
  have := flat_of_injective K (PowerSeries K) PowerSeries.C_injective
  let ρ : (E →+* ℂ) → 𝓞 E → K := fun τ x => algebraMap c.F K (embK c τ x)
  let M' : 𝓞 E → Matrix (Fin g) (Fin g) (PowerSeries K) := fun x => (M x).map (PowerSeries.C (R := K))
  have hM' : ∀ x i, IsLieComb (M' x i) v (v i ≫ W.t.act.act x) := hM
  choose u hu using fun τ k => (hu _ (ht τ k)).exists
  have img : ∀ τ k, LieImg W (e τ k) (prodPts (fun j => PowerSeries.C (R := K) (u τ k j)) v) := fun τ k =>
    (lin g _ e₀ _ v _ (fun i => (hev i).2) (hu τ k)).2 ((Chart.isLieComb_iff _ _ _).2 rfl)
  have p0 : prodPts 0 v = 1 := by
    simpa [prodPts] using (prodPts_prodPts hv.1 (m := 0) Fin.elim0 Fin.elim0).symm
  have eig : ∀ τ k x, u τ k ᵥ* M x = ρ τ x • u τ k := fun τ k x => funext fun i => PowerSeries.C_injective (R := K)
    (((PowerSeries.C (R := K)).map_vecMul (M x) (u τ k) i).trans
      ((congrFun ((eig_iff hv hM' _ _ _).1 (he τ k _ (img τ k) x)) i).trans (map_mul _ _ _).symm))
  have ind : ∀ τ, LinearIndependent K (u τ) := fun τ => Fintype.linearIndependent_iff.2 fun cf h => by
    obtain ⟨k₀, h₀, hk⟩ := hi τ
    obtain ⟨ν, hν⟩ := ConstLie.exists_gtComb cf (e τ)
    have z : ν.IsZero := isZero_of_lieImg W hG ((lin _ cf (e τ) ν _ 1 (img τ) hν).2 (by
      rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, ← p0]
      refine congrArg (prodPts · v) (funext fun j => ?_)
      have := congrArg (PowerSeries.C (R := K)) (congrFun h j)
      simpa [Finset.sum_apply] using this.symm))
    have hk' := hk cf ((b_of_gtComb hν).symm.trans z.1)
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [hk' k hk, zero_smul]) (by simp)] at h
    intro k
    by_cases hkk : k = k₀
    · subst hkk
      refine (smul_eq_zero.1 h).resolve_right fun h₁ => h₀ (isZero_of_lieImg W hG ?_)
      have := img τ k
      rwa [h₁, show (fun j => PowerSeries.C (R := K) ((0 : Fin g → K) j)) = 0 from funext fun _ => map_zero _,
        p0] at this
    · exact hk' k hkk
  have key : ∀ τ (w : Fin g → PowerSeries K), (∀ x, w ᵥ* M' x = PowerSeries.C (R := K) (ρ τ x) • w) →
      ∃! cf : Fin (Dw.mult τ) → PowerSeries K, w = ∑ k, cf k • (fun j => PowerSeries.C (R := K) (u τ k j)) := by
    intro τ
    obtain ⟨n, u', hu₁, hu'⟩ := (commonEigenvectors_flat_baseChange K (𝓞 E) g 0 M (ρ τ)).2
    have flat := (commonEigenvectors_flat_baseChange K (𝓞 E) g n M (ρ τ)).1 K u' hu₁ (by simpa using hu')
    have hm : ∀ x, (M' x).map ((algebraMap K F).comp PowerSeries.constantCoeff) = (M x).map (algebraMap K F) :=
      fun x => by ext i j; simp [M']
    obtain rfl := card_eq_of_lieMult hv hM' _ (lieMult_arc W F τ) (fun k j => algebraMap K F (u' k j))
      (fun k x => by
        rw [hm]
        exact vecMul_map _ (hu₁ k x))
      (fun w hw => flat F w fun i => (congrArg (w ᵥ* ·) (hm i)).symm.trans (hw i))
    exact (commonEigenvectors_flat_baseChange K (𝓞 E) g _ M (ρ τ)).1 K (u τ) (eig τ) (by
      simpa using fun w hw => existsUnique_comb (ind τ) (fun k => (hu' _ (eig τ k)).exists) (hu' w hw).exists)
      (PowerSeries K)
  refine ⟨_, img, fun τ => ⟨fun k => ⟨isTangent_prodPts hv.1 _, he τ k _ (img τ k)⟩, fun w hw he => ?_⟩⟩
  obtain ⟨d, rfl⟩ := exists_prodPts hv hw
  refine (existsUnique_congr fun cf => ?_).1 (key τ d fun x => (eig_iff hv hM' _ _ _).1 (he x))
  rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, (prodPts_injective hv).eq_iff]

end ThetaShiftProofs

section Main

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open GlobalTheory.LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem letter_eq {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} {c : Coeff l} {n₁ n₂ f : ℕ} {o : LamObj c n₁ n₂} {La : ℝ} (ho : LamObjGood o f La) {L : LamLetters o}
    (hL : L.IsGood) {m : Fin o.xB.P.g} {w : epsR o.K₁ ⟶ o.xB.P.A} (hw : L.IsLetter m w) :
    w = prodPts (L.U m) o.xB.v := by
  obtain ⟨w', h', hc⟩ := hL.2.2.1 m
  refine Eq.trans (Over.OverMorphism.ext (ho.2.2.2.1.1.1.hom_ext ?_ ((Over.w w).trans (Over.w w').symm)))
    ((Chart.isLieComb_iff _ _ _).1 hc)
  unfold LamLetters.IsLetter at hw h'
  generalize L.src m = q at hw h'
  cases q <;> exact hw.trans h'.symm

theorem main : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries K₁) ⟶ Y.X) (W : Wit Y (a.restrict β) χ), ArcLieBasis W e := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ a e th jj n' La c₁ s O _ β Y χ W
  letI := H.starRing
  have hG := hK.laws.globalFns
  obtain ⟨pl, pa, pt, -, -⟩ := pairE_properties E a.D₀.X s.ξ
  have hn : (n' : K₁) ≠ 0 := Nat.cast_ne_zero.2 s.n_pos.ne'
  refine arcLieBasis_of_indep W hG e s.tan (fun τ k v hv x => ?_) fun τ => ?_
  · cases hk : s.kind τ k with
    | none =>
      refine TorusType.main hG E H Dw l Xo c O β Y K₁ _ (a.restrict β) χ W
        (AddMonoidHom.mk' (fun y => labK c K₁ τ (cc (pairE s.ξ y))) fun y y' => ?_)
        ((algebraMap c.F K₁).comp (embK c τ)) (e τ k) v (fun x y => ?_) (s.tan τ k) (s.xi τ k hk).1 (s.xi τ k hk).2 hv x
      · refine (congrArg (fun q => labK c K₁ τ (cc q)) (pa y y')).trans ?_
        rw [cc, map_add, map_add]; rfl
      · refine (congrArg (fun q => labK c K₁ τ (cc q)) (pl (H.bar x) y)).trans ?_
        rw [H.bar_eq, cc, map_mul, map_mul, IsCMField.complexConj_apply_apply]; rfl
    | some m =>
      obtain ⟨w, hw, hp⟩ := s.eta τ k m hk
      have hm := ((s.full τ).2.2 m).1 ⟨k, hk⟩
      obtain ⟨w', h₁, h₂⟩ := LetterEigen.letter_eigen E H l c _ _ _ _ La s.good s.L s.L_good (s.L.e.symm m).1
        (s.L.e.symm m).2 w (by rw [Sigma.eta, Equiv.apply_symm_apply]; exact hw) x
      rw [hm] at h₁
      refine eig_of_isPull W hG hv x _ (isPull_smulPt_split hG a.oa s.split x _ _ ?_ hp)
      obtain ⟨u, hu, rfl⟩ := h₁
      refine Over.OverMorphism.ext (s.good.2.2.2.1.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      refine Eq.trans ?_ (h₂.trans (congrArg (· ≫ s.φB) ?_))
      · exact (Category.assoc _ _ _).trans (congrArg (w.left ≫ ·) (s.act x))
      · rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
        exact hu 0
  · obtain ⟨hinj, ⟨k₀, hk₀⟩, -⟩ := s.full τ
    refine ⟨k₀, fun hz => s.ξ_ne (LinearMap.ext fun y => ?_), fun cf h k hk => ?_⟩
    · have h₀ := dlog_eq_zero (s.tan τ k₀) hz (s.xi τ k₀ hk₀).2 y
      rw [map_eq_zero, cc, map_eq_zero] at h₀
      have := pt y
      rw [h₀, map_zero] at this
      exact_mod_cast this.symm
    · have p0 : prodPts 0 s.v = 1 := by
        simpa [prodPts] using (prodPts_prodPts s.basis.1 (m := 0) Fin.elim0 Fin.elim0).symm
      let U : Matrix (Fin a.D₀.P.g) (Fin a.D₀.P.g) K₁ := s.L.U
      have hb : ∀ k, (e τ k).b = prodPts ((s.kind τ k).elim 0 U) s.v := fun k => by
        cases hk : s.kind τ k with
        | none => exact (s.xi τ k hk).1.trans p0.symm
        | some m =>
          obtain ⟨w, hw, hp⟩ := s.eta τ k m hk
          have e₁ : w = prodPts (U m) s.v := letter_eq s.good s.L_good hw
          have e₂ : (e τ k).b = GrpTangent.epsScale (n' : K₁)⁻¹ ≫ (s.sB _ w).b := Over.OverMorphism.ext hp.1
          rw [e₂, s.split.1, GrpTangent.pow_eq_epsScale_comp (e₁ ▸ isTangent_prodPts s.basis.1 _),
            GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ hn, GrpTangent.epsScale_one, Category.id_comp]
          exact e₁
      rw [funext hb, prodPts_prodPts s.basis.1, ← p0] at h
      have h₁ : ∑ k, cf k • (s.kind τ k).elim 0 U = 0 := prodPts_injective s.basis h
      have hU : LinearIndependent K₁ U.row := Matrix.linearIndependent_rows_of_det_ne_zero
        (Ind.lamInd E H l c (fun _ => rfl) _ _ _ _ La s.good s.L s.L_good)
      have ne : ∀ k : {k // k ≠ k₀}, ∃ m, s.kind τ k = some m := fun k =>
        Option.ne_none_iff_exists'.1 fun h => k.2 (hinj (h.trans hk₀.symm))
      choose m hm using ne
      have hi := hU.comp m fun k k' h => Subtype.ext (hinj ((hm k).trans (h ▸ (hm k').symm)))
      refine Fintype.linearIndependent_iff.1 hi (fun k => cf k) ?_ ⟨k, hk⟩
      have z : cf k₀ • (s.kind τ k₀).elim 0 U = 0 := by rw [hk₀]; exact smul_zero _
      rw [Fintype.sum_eq_add_sum_subtype_ne _ k₀, z, zero_add] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h₁
      rw [hm]; rfl

end Main

end GlobalTheory.LetterBasis
