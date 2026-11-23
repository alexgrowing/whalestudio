import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf

noncomputable section

namespace GlobalTheory.ArcQ.FrLin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Const

variable {R : Type} [CommRing R] {X Z : Scheme.{0}}

theorem res_const (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem appLE_const (p : X ⟶ Sp R) (f : Z ⟶ X) {U : X.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn p U a) = constFn (f ≫ p) V a := by
  exact congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top h)

theorem const_spMap {S : Type} [CommRing S] (φ : R →+* S) (q : X ⟶ Sp S) (U : X.Opens) (a : R) :
    constFn (q ≫ spMap φ) U a = constFn q U (φ a) := by
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  unfold constFn
  rw [N, ← Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ U le_top le_top, CommRingCat.comp_apply]
  congr 2

def smulSec (p : X ⟶ Sp R) (a : R) {L : LB X} (s : LB.Sec L) : LB.Sec L where
  f j := constFn p _ a * s.f j
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, res_const, res_const]
    ring

theorem isoMaps_smul (p : X ⟶ Sp R) (a : R) {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M}
    (h : IsoMaps w s s') : IsoMaps w (smulSec p a s) (smulSec p a s') := by
  intro i k
  have e := h i k
  simp only [smulSec]
  rw [map_mul, map_mul, e, res_const, res_const]
  exact mul_left_comm _ _ _

end Const

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [SecCalc.spMap_comp', SecCalc.spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comb_transport {R S : Type} [CommRing R] [CommRing S] (io : R →+* S) {x : Sp S ⟶ Xo.X} {G : SAB H (Sp S)}
    {t : SAB H (Sp R)} (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t (spMap io)) {n : ℕ} (cf : Fin n → R)
    (v : Fin n → (epsR R ⟶ t.G)) (w : epsR R ⟶ t.G) (hw : IsLieComb cf v w) (q : Fin n → (epsR S ⟶ G.G))
    (hq : ∀ i, (q i).left ≫ m2.φ = spMap (dualMap io) ≫ (v i).left)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hu : IsCombAt x (fun i => (q i).left ≫ m1.φ) (fun i => io (cf i)) u) :
    ∃ u' : Sp (DualNumber S) ⟶ G.G.left, u' ≫ m1.φ = u ∧ u' ≫ m2.φ = spMap (dualMap io) ≫ w.left ∧
      u' ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := by
  have wb : w.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  have cond : (spMap (dualMap io) ≫ w.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, wb, dual_alg]
  let w' : epsR S ⟶ G.G := Over.homMk (m2.cart.1.lift _ _ cond) (m2.cart.1.lift_snd _ _ cond)
  have hw' : w'.left ≫ m2.φ = spMap (dualMap io) ≫ w.left := m2.cart.1.lift_fst _ _ cond
  have hc : IsLieComb (fun i => io (cf i)) q w' := Chart.comb_baseChange io m2.cart hw hq hw'
  obtain ⟨p, hp, hpp⟩ := (Chart.comb_push m1.cart _ _ _).1 hc
  obtain ⟨p', hp', hpp'⟩ := hu
  obtain rfl : p = p' := funext fun i => Over.OverMorphism.ext ((hp i).trans (hp' i).symm)
  exact ⟨w'.left, hpp.symm.trans hpp', hw', Over.w w'⟩

end GlobalTheory.ArcQ.FrLin

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.ArcQ.FrLin

theorem isArcFr_of_frChg_const : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W e e' th th' g r hth hg hr S _ _ io y y' _ hy hchg
  obtain ⟨x', xo', u', t1', t2', t3', s', t4'⟩ := y'
  obtain ⟨hx, hcomb, hs⟩ := hchg
  dsimp only at hx hcomb hs
  subst hx
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, ps, hgx⟩ := hy
  have key : ∀ τ k, ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (q : epsR S ⟶ G.G), LieImg W (e τ k) v ∧
      q.left ≫ m1.φ = y.u τ k ∧ q.left ≫ m2.φ = spMap (dualMap io) ≫ v.left := fun τ k => by
    obtain ⟨v, p, h1, h2, h3, h4⟩ := hu τ k
    exact ⟨v, Over.homMk p h4, h1, h2, h3⟩
  choose v q hv hq1 hq2 using key
  have hθ' : ThetaOf W th' (smulSec W.t.G.hom (PowerSeries.C (R := A) r) θ) :=
    (((GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth).2 θ hθ).2.2 r th' _ hr).2 fun _ => rfl
  have hs' : ∀ i, s'.f i = scal y.x (io (PowerSeries.C (R := A) r)) i * y.s.f i :=
    ((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
      (by rw [SecCalc.spMap_id', Category.id_comp]) (by rw [SecCalc.spMap_id', Category.id_comp])).2.1 _ _ _).1 hs
  refine ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, fun τ k => ?_, _, w1, w2,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) σ, smulSec G.G.hom (io (PowerSeries.C (R := A) r)) s1,
    smulSec G.G.hom (io (PowerSeries.C (R := A) r)) θ2, hθ', r1, r2, isoMaps_smul _ _ i1, isoMaps_smul _ _ i2,
    fun j h => ?_, fun gx g1 g2 j h => ?_⟩
  · obtain ⟨w, hw, -⟩ := (GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c O β Y A b a χ W (e' τ k)).1
    have hc := (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e τ) (e' τ k) (v τ) w (hv τ)
      (hg τ k)).1 hw
    have hy : y.u τ = fun i => (q τ i).left ≫ m1.φ := funext fun i => (hq1 τ i).symm
    obtain ⟨p, p1, p2⟩ := comb_transport io m1 m2 _ (v τ) w hc (q τ) (hq2 τ) (u' τ k) (hy ▸ hcomb τ k)
    exact ⟨w, p, hw, p1, p2⟩
  · show constFn _ _ _ * θ2.f j = (m2.φ.appLE _ _ h).hom (constFn _ _ _ * θ.f _)
    rw [map_mul, ← ps j h, appLE_const, m2.cart.1.w, const_spMap]
  · refine Eq.trans ?_ (congrArg (gx.appLE _ _ h).hom (hs' _)).symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ (hgx gx g1 g2 j h)
    exact ((appLE_const _ gx h _).trans (congrArg (fun p => constFn p _ _) g2)).symm

end GlobalTheory.ArcQ
