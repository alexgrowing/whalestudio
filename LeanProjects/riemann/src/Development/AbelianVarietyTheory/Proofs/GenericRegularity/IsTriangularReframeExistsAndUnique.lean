import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

noncomputable section

namespace GlobalTheory.Reg.ReframeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

def toM {x : Sp S ⟶ Xo.X} {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT (t := Xo.univ.t) hv)

theorem comb_iff {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x v cf w ↔ (tv (∑ i, cf i • toM (hv i))).left = w := by
  have e := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) cf w
  refine e.trans ?_
  rw [tv_comb]
  rfl

theorem comb_unique {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' :=
  ((comb_iff hv cf w).1 h).symm.trans ((comb_iff hv cf w').1 h')

theorem comb_single {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (i : Fin m) : IsCombAt x v (Pi.single i 1) (v i) := by
  rw [comb_iff hv]
  have : ∑ j, (Pi.single i (1 : S) : Fin m → S) j • toM (hv j) = toM (hv i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [this]
  rfl

theorem comb_exists [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (τ : E →+* ℂ)
    (hv : ∀ j, IsTanAt x (v j)) (he : ∀ j, IsEigAt c τ (v j)) (cf : Fin m → S) :
    ∃ w, IsCombAt x v cf w ∧ IsTanAt x w ∧ IsEigAt c τ w := by
  refine ⟨_, (comb_iff hv cf _).2 rfl, isTanAtG_of (t := Xo.univ.t) _ (tv_zero' _), ?_⟩
  refine (isEigAt_iff τ (tv (∑ i, cf i • toM (hv i)))).2 fun a => ?_
  have hU : ∀ i, actL (x0 := x) Xo.univ.t.act a (toM (hv i)) = algebraMap c.F S (embK c τ a) • toM (hv i) :=
    fun i => tv_injective ((isEigAt_iff τ (ovT (t := Xo.univ.t) (hv i))).1 (he i) a)
  have : actL (x0 := x) Xo.univ.t.act a (∑ i, cf i • toM (hv i)) =
      algebraMap c.F S (embK c τ a) • ∑ i, cf i • toM (hv i) := by
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hU, smul_comm]
  exact congrArg tv this

theorem exists_reframe [Algebra c.F S] (y : FrPt Xo c S)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hg : ∀ τ, IsUnit (g τ).det) :
    ∃ y', Reframe g y y' := by
  choose u hu ht he using fun τ i => comb_exists τ (y.tan τ) (y.eig τ) (fun j => g τ j i)
  refine ⟨⟨y.x, y.x_over, u, ht, he, fun τ w hw hw' => ?_, y.s, y.gen⟩, rfl, hu⟩
  obtain ⟨a, ha, hua⟩ := y.basis τ w hw hw'
  have key : ∀ b w', IsCombAt y.x (u τ) b w' → IsCombAt y.x (y.u τ) ((g τ).mulVec b) w' := fun b w' h =>
    GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u τ) (g τ) b w' (hu τ) h
  refine ⟨(g τ)⁻¹.mulVec a, ?_, fun b hb => ?_⟩
  · obtain ⟨w', h1, -, -⟩ := comb_exists τ (ht τ) (he τ) ((g τ)⁻¹.mulVec a)
    have h2 := key _ _ h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mulVec] at h2
    show IsCombAt y.x (u τ) ((g τ)⁻¹.mulVec a) w
    rw [comb_unique (y.tan τ) ha h2]
    exact h1
  · rw [← hua _ (key b w hb), Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mulVec]

theorem existsUnique_reframe [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  have ht' : ∀ τ i, IsTanAt y.x (y'.u τ i) := fun τ i => hx ▸ y'.tan τ i
  have hb' : ∀ τ w, IsTanAt y.x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt y.x (y'.u τ) a w := by
    rw [← hx]; exact y'.basis
  choose a ha hua using fun τ i => y.basis τ (y'.u τ i) (ht' τ i) (y'.eig τ i)
  choose b hb _ using fun τ i => hb' τ (y.u τ i) (y.tan τ i) (y.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => a τ i j, ⟨fun τ => ?_, hx, ha⟩, fun g hg => ?_⟩
  · have hm : (Matrix.of fun j i => a τ i j) * (Matrix.of fun j i => b τ i j) = 1 := by
      ext j i
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (y'.u τ)
        (Matrix.of fun j i => a τ i j) (b τ i) (y.u τ i) (ha τ) (hb τ i)
      have h2 := (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique h1 (comb_single (y.tan τ) i)
      have h3 := congrFun h2 j
      rw [Pi.single_apply] at h3
      rw [Matrix.one_apply, ← h3]
      rfl
    exact Matrix.isUnit_det_of_right_inverse hm
  · funext τ
    ext j i
    exact congrFun (hua τ i _ (hg.2.2 τ i)) j

theorem reframe_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨exists_reframe y, existsUnique_reframe y⟩

end GlobalTheory.Reg.ReframeEx
