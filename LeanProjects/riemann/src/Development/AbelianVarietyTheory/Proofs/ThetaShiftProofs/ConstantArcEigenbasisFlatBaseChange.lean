import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroupStatement

noncomputable section

namespace GlobalTheory.BasisUniv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp JetR IsTan
open scoped CategoryTheory.Obj

section Coord

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem isUnivChart_iso {G' : Over (Spec (CommRingCat.of S))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_chart_of_pullback {R : Type} [CommRing R] [IsLocalRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    [Smooth G₀.hom] (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G), IsUnivChart G n x := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', -⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  exact ⟨n, _, isUnivChart_iso e hx'⟩

variable {n : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hy : IsUnivChart G n y)
  {g : ℕ} {v : Fin g → (epsR S ⟶ G)}
include hy

theorem isTangent_of_comb (hv : ∀ i, IsTangent (v i)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) :
    IsTangent w := by
  obtain ⟨k, -⟩ := prodPts_tan hy z v fun i => (isTan_iff _).2 (hv i)
  rw [(isLieComb_iff _ _ _).1 hw]
  exact (isTan_iff _).1 k

theorem coord_inj (hv : IsLieBasis v) (tv : ∀ i, IsTan (v i)) {c c' : Fin g → S}
    (h : ∑ i, c i • tcoord hy (v i) (tv i) = ∑ i, c' i • tcoord hy (v i) (tv i)) : c = c' := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v tv
  exact (hv.2 _ ((isTan_iff _).1 k)).unique ((comb_iff_coord hy c tv k).2 e)
    ((comb_iff_coord hy c' tv k).2 (e.trans h))

theorem comb_iff (hv : IsLieBasis v) {m : ℕ} {u : Fin m → (epsR S ⟶ G)} {U : Fin m → Fin g → S}
    (hU : ∀ k, IsLieComb (U k) v (u k)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (cf : Fin m → S) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun k => (isTan_iff _).2 (isTangent_of_comb hy hv.1 (hU k))
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have e : ∑ i, cf i • tcoord hy (u i) (tu i) = ∑ j, (∑ k, cf k • U k) j • tcoord hy (v j) (tv j) := by
    simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_comm
  rw [comb_iff_coord hy cf tu tw, e, (comb_iff_coord hy z tv tw).1 hw]
  exact ⟨fun q => coord_inj hy hv tv q, fun q => by rw [q]⟩

theorem tcoord_comp (f : G ⟶ G) [IsMonHom f] {w : epsR S ⟶ G} (tw : IsTan w) :
    tcoord hy (w ≫ f) (isTan_comp tw f) = tmap hy f (tcoord hy w tw) :=
  tcoord_congr hy (congrArg (· ≫ f) (tcoord_spec hy w tw)) _ (isTan_comp (isTan_tvec hy _) f)

theorem eig_iff (hv : IsLieBasis v) (f : G ⟶ G) [IsMonHom f] {M : Matrix (Fin g) (Fin g) S}
    (hM : ∀ i, IsLieComb (M i) v (v i ≫ f)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (r : S) :
    (w ≫ f).left = Geo.Tor.spMap (epsScaleR r) ≫ w.left ↔ z ᵥ* M = r • z := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have ew := (comb_iff_coord hy z tv tw).1 hw
  have e1 : tcoord hy (w ≫ f) (isTan_comp tw f) = ∑ j, (z ᵥ* M) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_comp hy f tw, ew, map_sum]
    simp only [map_smul, ← tcoord_comp hy f, (comb_iff_coord hy _ tv (isTan_comp (tv _) f)).1 (hM _),
      Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have e2 : tcoord hy (spMap (scaleD r) ≫ w) (isTan_scale r tw) = ∑ j, (r • z) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_scale hy r tw, ew, Finset.smul_sum]
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w := Over.OverMorphism.ext q
    exact coord_inj hy hv tv (e1.symm.trans ((tcoord_congr hy q' _ _).trans e2))
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w :=
      tan_ext hy (isTan_comp tw f) (isTan_scale r tw) (by rw [e1, e2, q])
    exact congrArg (fun t => t.left) q'

omit hy in

theorem exists_lift {R : Type} [CommRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) (w : epsR R ⟶ G₀) :
    ∃ w' : epsR S ⟶ G, w'.left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ w.left := by
  have c : (Geo.Tor.spMap (dualMapR f) ≫ w.left) ≫ G₀.hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    rw [Category.assoc, Over.w w]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg Geo.Tor.spMap (RingHom.ext fun r => by
      ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl])).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.1.lift _ _ c) (h.1.lift_snd _ _ c), h.1.lift_fst _ _ c⟩

end Coord

theorem eig_powerSeries {A : Type} [CommRing A] [IsNoetherianRing A] {I : Type} {g m : ℕ}
    (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    {S : Type} [CommRing S] (f : A →+* S) (hf : f.Flat) (w : Fin g → S)
    (hw : ∀ i, w ᵥ* (M i).map f = f (ρ i) • w) : ∃! cf : Fin m → S, w = ∑ k, cf k • fun j => f (U k j) := by
  let _ := f.toAlgebra
  have : Module.Flat A S := hf
  refine (GlobalTheory.commonEigenvectors_flat_baseChange A I g m M ρ).1 A U hU (fun z hz => ?_) S w hw
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  obtain ⟨cf, hcf, huniq⟩ := h (fun j => PowerSeries.C (R := A) (z j)) (fun i => by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun (hz i) j)
    simpa [Matrix.vecMul, dotProduct] using this)
  have key : ∀ c : Fin m → A, (z = ∑ k, c k • fun j => U k j) →
      (fun k => PowerSeries.C (R := A) (c k)) = cf := fun c hc => huniq _ (by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun hc j)
    simpa [Finset.sum_apply] using this)
  refine ⟨fun k => PowerSeries.constantCoeff (R := A) (cf k), ?_, fun c hc => ?_⟩
  · funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun hcf j)
    simpa [Finset.sum_apply] using this
  · rw [← key c hc]
    funext k
    simp

end GlobalTheory.BasisUniv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

open Matrix GlobalTheory.BasisUniv in

theorem GlobalTheory.ArcQ.arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart

  have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
    have ht : GtTanR (e τ k) :=
      ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
    obtain ⟨U, hU, -⟩ := hcomb _ ht
    exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
  choose U hU using hU
  choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
  choose v' hv' using fun j => exists_lift ι m2.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
  have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
    Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
  have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
      rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
    have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
    fun w hw hwe => ?_⟩⟩
  · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
    funext j
    have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨z, hz, -⟩ := hb'.2 w hw
    simp only [comb_iff hy' hb' (hU' τ) hz]
    refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
      (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
    have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv (hU τ) hc] using this
