import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.IntChg

section Sec

variable {X Y : Scheme.{0}}

def mulSec {L : LB X} (r : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top r * s.f i
  compat i j := by
    have e : ∀ (U : X.Opens) (h : L.U i ⊓ L.U j ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := fun U h => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem res_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_res (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, ⊤)) :
    (f.appLE U V h).hom (resG X le_top r) = resG Y le_top (f.appTop.hom r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem isoMaps_mul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (r : Γ(X, ⊤)) : IsoMaps w (mulSec r s) (mulSec r s') := by
  intro i k
  have := h i k
  simp only [mulSec, map_mul, res_res]
  rw [this, mul_left_comm]

theorem pullSec_mul {L : LB X} {f : Y ⟶ X} {s : LB.Sec L} {s' : LB.Sec (L.pull f)} (h : PullSec f s s')
    (r : Γ(X, ⊤)) : PullSec f (mulSec r s) (mulSec (f.appTop.hom r) s') := by
  intro j hj
  simp only [mulSec, map_mul, appLE_res]
  rw [h j hj]

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

end Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem integral_scal (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (a : T.Vˣ) (s' : LB.Sec (PPx y.x))
      (hg : ∀ s'' : LB.Sec (PPx y.x), ∃! b : T.Fr, ∀ i, s''.f i = scal y.x b i * s'.f i),
      (∀ i, s'.f i = scal y.x (algebraMap T.V T.Fr a) i * y.s.f i) → Integral T io y →
      Integral T io { y with s := s', gen := hg } := by
  let _ := io.toAlgebra
  intro y a s' hg hs h
  obtain ⟨G, t', m1, m2, hu, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hl⟩ := h
  have hc : m2.φ.appTop.hom (G.G.hom.appTop.hom (toΓ T.V a)) =
      t'.G.hom.appTop.hom (toΓ T.Fr (algebraMap T.V T.Fr a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, m2.cart.1.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    exact congrArg _ (appTop_toΓ _ _)
  refine ⟨G, t', m1, m2, hu, mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ, fun τ => ?_, w1, w2, _, _, _, r1, r2,
    isoMaps_mul i1 _, isoMaps_mul i2 _, pullSec_mul hp _, ?_⟩
  · obtain ⟨b, hb, hbu⟩ := hθ τ
    have key : ∀ (d : T.V) i, resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V d)) *
        (mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ).f i =
        resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V (d * a))) * θ.f i := fun d i => by
      simp only [mulSec, map_mul, _root_.mul_assoc]
    refine ⟨b * ↑a⁻¹, fun i => ?_, fun d hd => ?_⟩
    · rw [key, Units.inv_mul_cancel_right]; exact hb i
    · rw [← hbu (d * a) fun i => by rw [← key]; exact hd i, Units.mul_inv_cancel_right]
  · intro g e1 e2 j hj
    have e3 := hl g e1 e2 j hj
    show resG _ le_top _ * s1.f j = (g.appLE _ _ hj).hom (s'.f _)
    refine Eq.symm ((congrArg _ (hs _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ e3.symm)))
    refine (appLE_res g _ _ hj _).trans (congrArg _ ?_)
    rw [hc, ← e2, Scheme.Hom.comp_appTop]
    rfl

theorem integral_chg (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y y' : FrPt Xo c T.Fr) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (a : T.Vˣ),
      (∀ τ, IsUnit (k τ).det) → FrChg (fun τ => (k τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr a) y y' →
      Integral T io y → Integral T io y' := by
  let _ := io.toAlgebra
  intro y y' k a hk ⟨hx, hu, pm, h1, h2, h3⟩ hy
  have hk' : ∀ τ, IsUnit (k τ).transpose.det := fun τ => by rw [Matrix.det_transpose]; exact hk τ
  have hK : ∀ τ, IsUnit ((k τ).transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (k τ).transpose) hk' hK
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := y'
  simp only at hx
  subst hx
  have eu : zu = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hu τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  subst eu
  have ep : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · refine h2.trans ?_
      simp only [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
      rfl
    · exact h1.trans (Category.id_comp _).symm
  subst ep
  refine integral_scal T io (GlobalTheory.IntRebase.rebase₂ y _ hK) a zs zg (fun i => ?_) hr
  exact (h3 i le_rfl).symm.trans (GlobalTheory.IntRebase.id_appLE_apply _ _ _ _)

theorem integral_of_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (s : T.V), (∀ τ, IsUnit (g τ).det) → IsUnit s → letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, FrChg (fun τ => (g τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr s) y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c T io g s hg hs y y' h hy
  obtain ⟨a, rfl⟩ := hs
  exact integral_chg T io y y' g a hg h hy

end GlobalTheory.ArcQ.IntChg
