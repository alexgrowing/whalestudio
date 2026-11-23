import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

noncomputable section

namespace GlobalTheory.ConstModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

section Bundles

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def SecThrough (w : LB.Iso L' (L.pull Φ)) (s : LB.Sec L) (s' : LB.Sec L') : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, Φ (r z) ∈ L.U j → r z ∈ L'.U k →
    gs (r ≫ Φ) z _ (s.f j) = (Geo.Tor.gw w r z j k).val * gs r z _ (s'.f k)

theorem SecThrough.mem {w : LB.Iso L' (L.pull Φ)} {s : LB.Sec L} {s' : LB.Sec L'} (h : SecThrough w s s')
    (hL' : L'.IsLB) {x : X'} (hx : Φ x ∈ nonzeroLocus s) : x ∈ nonzeroLocus s' := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hj' : Φ x ∈ L.U j := X.basicOpen_le _ hj
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have u : IsUnit (gs (𝟙 X) (Φ x) _ (s.f j)) := by
    rw [gs_eq (𝟙 X) (Φ x) _ hj']; exact (X.mem_basicOpen _ _ hj').1 hj
  have e := h _ (𝟙 _) x j k hj' hk
  rw [Category.id_comp, gs_stalkMap Φ x _ hj'] at e
  have u' : IsUnit (gs (𝟙 X') x _ (s'.f k)) := isUnit_of_mul_isUnit_right (e ▸ u.map _)
  rw [gs_eq (𝟙 X') x _ hk] at u'
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (X'.mem_basicOpen _ _ hk).2 u'⟩

end Bundles

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}

def Vanishes (k : T' ⟶ T) (g : GtPt D T) : Prop :=
  k ≫ g.b = 1 ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J, Good D.P.L z J → val (g.s χ) (r ≫ k.left) z J = 1

theorem Vanishes.comp {k : T' ⟶ T} {g : GtPt D T} (h : Vanishes k g) (k' : T'' ⟶ T') : Vanishes (k' ≫ k) g :=
  ⟨by rw [Category.assoc, h.1, MonObj.comp_one], fun χ Z r z J hJ => by
    rw [Over.comp_left, ← Category.assoc]; exact h.2 χ Z _ z J hJ⟩

def epsZero (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

end Points

section Through

variable {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R'']
  {f : R →+* R'} {f' : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''}

def Through (p : IsPullDeg f D D') {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (g : GtPt D T)
    (g' : GtPt D' T') : Prop :=
  ∀ y, (∀ k, DegPre.gtφT D' T' g'.b y k ≫ proj p = h ≫ DegPre.gtφT D T g.b (p.xe y) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g.s (p.xe y)) (r ≫ h) z J =
        (∏ k, om p.w z J J' (r ≫ DegPre.gtφT D' T' g'.b y k) ^ DegPre.gtε k) * val (g'.s y) r z J'

structure IsComp (p : IsPullDeg f D D') (q : IsPullDeg f' D' D'') (r : IsPullDeg (f'.comp f) D D'') : Prop where
  proj_eq : proj r = proj q ≫ proj p
  xe_eq : ∀ x, r.xe x = p.xe (q.xe x)
  tri : ∀ (Y : Scheme.{0}) (x : Y ⟶ D''.P.A.left) (y : Y) j i k, proj p (proj q (x y)) ∈ D.P.L.U j →
    proj q (x y) ∈ D'.P.L.U i → x y ∈ D''.P.L.U k →
    Geo.Tor.gw r.w x y j k = Geo.Tor.gw p.w (x ≫ proj q) y j i * Geo.Tor.gw q.w x y i k

namespace IsComp

variable {p : IsPullDeg f D D'} {q : IsPullDeg f' D' D''} {r : IsPullDeg (f'.comp f) D D''} (C : IsComp p q r)
include C

theorem om_eq {Z : Scheme.{0}} {z : Z} {J J' J''} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (hJ'' : Good D''.P.L z J'') (x : Z ⟶ D''.P.A.left) :
    om r.w z J J'' x = om p.w z J J' (x ≫ proj q) * om q.w z J' J'' x := by
  have e : x ≫ proj r = (x ≫ proj q) ≫ proj p := (congrArg (x ≫ ·) C.proj_eq).trans (Category.assoc _ _ _).symm
  exact (congrArg (fun u => Geo.Tor.gw r.w x z (J u) (J'' x)) e).trans
    (C.tri Z x z _ _ _ (hJ ((x ≫ proj q) ≫ proj p)) (hJ' (x ≫ proj q)) (hJ'' x))

theorem isPullGtF {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    [Algebra (FractionRing R'') F] (hF : Compat (f'.comp f) F) (hF' : Compat f' F) {g : GtPtF D F} {g' : GtPtF D' F}
    {g'' : GtPtF D'' F} (H : IsPullGtF f p F g g') (H' : IsPullGtF f' q F g' g'') :
    IsPullGtF (f'.comp f) r F g g'' := by
  refine isPullGtF_of_val r hF ?_ fun χ y J J'' hJ hJ'' => ?_
  · rw [C.proj_eq, ← Category.assoc]
    exact (congrArg (· ≫ proj p) H'.1).trans H.1
  · obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    have v := pullGt_val p H (q.xe χ) (𝟙 _) hJ hJ'
    have v' := pullGt_val q H' χ (𝟙 _) hJ' hJ''
    obtain ⟨hψ, -⟩ := H'.2 χ
    have a₀ : (cP D'' _ χ * g''.b).left ≫ proj q = 𝟙 _ ≫ (cP D' _ (q.xe χ) * g'.b).left := hψ 0
    have a₁ : (cP D'' (TF (R := R'') F) χ).left ≫ proj q = 𝟙 _ ≫ (cP D' (TF (R := R') F) (q.xe χ)).left := hψ 1
    have a₂ : g''.b.left ≫ proj q = 𝟙 _ ≫ g'.b.left := hψ 2
    have a₃ : (1 : TF (R := R'') F ⟶ D''.P.A).left ≫ proj q = 𝟙 _ ≫ (1 : TF (R := R') F ⟶ D'.P.A).left := hψ 3
    simp only [Category.id_comp] at v'
    rw [C.xe_eq, C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', C.om_eq hJ hJ' hJ'', a₀, a₁, a₂, a₃]
    have alg : ∀ (U : Type) [CommGroup U] (a b c d a' b' c' d' v : U), a⁻¹ * b * c * d⁻¹ * (a'⁻¹ * b' * c' * d'⁻¹ * v) =
        (a * a')⁻¹ * (b * b') * (c * c') * (d * d')⁻¹ * v := fun U _ a b c d a' b' c' d' v => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact (v.trans (congrArg₂ (· * ·) rfl v')).trans (alg _ _ _ _ _ _ _ _ _ _)

end IsComp

end Through

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : Formalism.L2.Pj.CDVR :=
  haveI : CharZero (PowerSeries K) := algebraRat.charZero _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ⟨PowerSeries K⟩

def powerSeriesConst (K : Type) [Field K] [CharZero K] : K →+* (powerSeriesCDVR K).V := PowerSeries.C (R := K)

end GlobalTheory.ConstModel
