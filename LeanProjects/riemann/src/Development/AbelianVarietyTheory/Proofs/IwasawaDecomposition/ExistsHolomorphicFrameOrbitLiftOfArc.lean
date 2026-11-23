import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstSubstitutionOfHolomorphicFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFramesSamePeriodCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEqStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.ArcLift

open scoped Matrix

section Adapted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
    (fun j => Formalism.L2.PjFree.relab c σ (e j).1))

def Adp (y : FrPt Xo c (CAt σ)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) : Prop :=
  IsPeriod (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ y.x = F.u k P ∧
    ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)

def Lev (D : Datum H) (l : Level H) : Type :=
  {δ : D.La ≃ₗ[𝓞 E] D.La // (∀ a b, D.EF (δ a) (δ b) = D.EF a b) ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, δ a = a + l.M • e) ∧
    ∀ a, ∃ e, δ a = a + l.A • e}

instance (D : Datum H) (l : Level H) : Countable (Lev D l) := by
  have := GlobalTheory.FibreMatch.countable_La D
  have := D.fin
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := 𝓞 E) (M := D.La)
  refine Function.Injective.countable (f := fun (δ : Lev D l) (i : Fin n) => δ.1 (v i)) fun δ δ' h => ?_
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (LinearMap.ext_on_range hv fun i => congrFun h i))

variable {F}

theorem Adp.comp {y : FrPt Xo c (CAt σ)} {k : Fin F.n} {P : (F.Di k).La →+ (Fin g → ℂ)} (hP : Adp F y k P)
    (δ : Lev (F.Di k) l) : Adp F y k (P.comp δ.1.toLinearMap.toAddMonoidHom) := by
  obtain ⟨δ, h1, h2, h3⟩ := δ
  obtain ⟨hP, hx, hd⟩ := hP
  have hr : Set.range (P.comp δ.toLinearMap.toAddMonoidHom) = Set.range P := δ.surjective.range_comp P
  have hQ : IsPeriod (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (P.comp δ.toLinearMap.toAddMonoidHom) := by
    obtain ⟨a1, a2, a3, a4, Hm, a5, a6, a7⟩ := hP
    refine ⟨fun a x i => ?_, a2.comp δ.injective, ?_, by rw [hr, a4], Hm, a5, a6, fun x y => ?_⟩
    · have := a1 a (δ x) i
      rw [← map_smul] at this
      exact this
    · have : (P.comp δ.toLinearMap.toAddMonoidHom).range = P.range := SetLike.coe_injective hr
      rw [this]
      exact a3
    · rw [← h1]
      exact a7 _ _
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k _ P δ 1 hQ hP h1 h2 h3
    (fun a => by rw [Matrix.one_mulVec]; rfl)
  refine ⟨hQ, hx.trans hu.symm, fun τ i => ?_⟩
  simp only [Matrix.one_mulVec] at hex
  simp only [← hex]
  exact hd τ i

theorem Adp.exists_lev {y : FrPt Xo c (CAt σ)} {k : Fin F.n} {P P' : (F.Di k).La →+ (Fin g → ℂ)} (hP : Adp F y k P)
    (hP' : Adp F y k P') : ∃ δ : Lev (F.Di k) l, ∀ a, P' a = P (δ.1 a) := by
  obtain ⟨hP, hx, hd⟩ := hP
  obtain ⟨hP', hx', hd'⟩ := hP'
  obtain ⟨δ, h, h1, h2, h3, h4⟩ := (F.fibre k P' P hP' hP).1 (hx'.symm.trans hx)
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P' P δ
    (LinearMap.toMatrix' h.toLinearMap) hP' hP h1 h2 h3 (fun a => by rw [LinearMap.toMatrix'_mulVec]; exact h4 a)
  simp only [LinearMap.toMatrix'_mulVec] at hex
  obtain ⟨ht1, -, ht3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hh : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
    have := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P' hP' k P h.toLinearMap hP hex _ _).1 (hd' τ i)
    rw [Pi.basisFun_apply]
    exact (ht3 _ (ht1 _ _ (hd τ i))).unique this (hd τ i)
  refine ⟨⟨δ, h1, h2, h3⟩, fun a => ?_⟩
  rw [h4]
  exact (LinearMap.congr_fun hh _).symm

theorem Adp.sameLie {y y' : FrPt Xo c (CAt σ)} {k : Fin F.n} {P : (F.Di k).La →+ (Fin g → ℂ)} (hP : Adp F y k P)
    (hP' : Adp F y' k P) : SameLie y y' :=
  ⟨hP.2.1.trans hP'.2.1.symm, fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP.1).2.1 _).unique (hP.2.2 τ i) (hP'.2.2 τ i)⟩

variable (F)

set_option maxHeartbeats 1000000 in

theorem exists_adp_local {R : Type} [CommRing R] (xR : Sp R ⟶ Xo.X)
    (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) {m : ℕ}
    (ev : (Fin m → ℂ) → (R →+* ℂ)) {B : Set (Fin m → ℂ)} (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (hB : IsOpen B)
    (hφ : ∀ t, DifferentiableOn ℂ (fun u => ev u t) B)
    (hy : ∀ u ∈ B, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧
      ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧
      (∀ a, DifferentiableOn ℂ (fun b => P b a) B') ∧ ∀ b ∈ B', Adp F (y b) k (P b) := by
  have h₁ : IsHolTo B (fun b => spMap (ev b)) := ThetaValueCont.isHolTo_spMap hB ev hφ
  have h₂ : IsHolTo B (fun b => spMap (ev b) ≫ xR) :=
    HolHom.isHolTo_of_holAt hB fun z hz => (HolHom.holAt_of_isHolTo h₁ hz).comp _
  have h₃ : IsHolTo (X := Xo.X) B (fun b => (y b).x) := LocLift.isHolTo_congr h₂ fun b hb => (hy b hb).1
  obtain ⟨B', k, P₁, hB', hb', hsub, hP₁, hu⟩ := F.lift m B (fun b => (y b).x) hB (fun b _ => (y b).x_over) h₃ b₀ hb₀
  choose! w V P hw hV hPe hP hx hd using fun b (hb : b ∈ B') =>
    GlobalTheory.AdaptedPeriods.exists_adapted E H Dw l Xo c σ g e F (y b) k (P₁ b) (hP₁.1 b hb) (hu b hb)
  refine ⟨B', k, P, hB', hb', fun a b hb => ?_, fun b hb => ⟨hP b hb, hx b hb, hd b hb⟩⟩
  have hwd : ∀ j, DifferentiableAt ℂ (fun b => w b j) b := fun j => by
    refine HolFrameMatrix.differentiableAt_coord F k (vR (e j).1 (e j).2) ev hB' hP₁ (fun b => w b j)
      (fun b hb => ?_) hb fun t => (hφ t).differentiableAt (hB.mem_nhds (hsub hb))
    have := hw b hb j
    rw [(hy b (hsub hb)).2] at this
    rw [← HolFrameMatrix.dualMap_eq]
    exact this
  have hVd : ∀ i j, DifferentiableAt ℂ (fun b => V b i j) b :=
    HolFrameMatrix.differentiableAt_of_mul_eq_one V (fun b => Matrix.of fun i j => w b j i) b
      (fun i j => differentiableAt_pi.1 (hwd j) i) (by
        filter_upwards [hB'.mem_nhds hb] with t ht
        ext i j
        have := congrFun (hV t ht j) i
        rw [Matrix.mul_apply, Matrix.one_apply]
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this)
  refine DifferentiableWithinAt.congr (f := fun b => V b *ᵥ P₁ b a) ?_ (fun t ht => hPe t ht a) (hPe b hb a)
  refine differentiableWithinAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact DifferentiableWithinAt.fun_sum fun j _ =>
    (hVd i j).differentiableWithinAt.mul (differentiableWithinAt_pi.1 (hP₁.2 a b hb) j)

theorem exists_adp_global (y : ℂ → FrPt Xo c (CAt σ)) (T : ℝ) (hper : ∀ w, y (w + 1) = y w)
    (hloc : ∀ w : ℂ, T < w.im → ∃ (k : Fin F.n) (P : ℂ → ((F.Di k).La →+ (Fin g → ℂ))),
      ∀ᶠ z in 𝓝 w, Adp F (y z) k (P z) ∧ ∀ a, DifferentiableAt ℂ (fun b => P b a) z)
    (k : Fin F.n) {w₀ : ℂ} (hw₀ : T < w₀.im) {P₀ : (F.Di k).La →+ (Fin g → ℂ)}
    (hP₀ : IsPeriod (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P₀) (hx₀ : (y w₀).x = F.u k P₀) :
    ∃ (P : ℂ → ((F.Di k).La →+ (Fin g → ℂ))) (δ : Lev (F.Di k) l),
      (∀ a, DifferentiableOn ℂ (fun b => P b a) {w : ℂ | T < w.im}) ∧
      ∀ w : ℂ, T < w.im → Adp F (y w) k (P w) ∧ ∀ a, P (w + 1) a = P w (δ.1 a) := by
  have hcv : Convex ℝ {w : ℂ | T < w.im} := convex_halfSpace_im_gt T
  have hop : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  haveI : Nonempty (Fin F.n) := ⟨k⟩
  have hidx : ∀ w : ℂ, T < w.im → ∃ P : ℂ → ((F.Di k).La →+ (Fin g → ℂ)),
      ∀ᶠ z in 𝓝 w, Adp F (y z) k (P z) ∧ ∀ a, DifferentiableAt ℂ (fun b => P b a) z := by
    have hl : ∀ w : ℂ, T < w.im → ∃ k : Fin F.n, ∃ P : ℂ → ((F.Di k).La →+ (Fin g → ℂ)),
      ∀ᶠ z in 𝓝 w, Adp F (y z) k (P z) ∧ ∀ a, DifferentiableAt ℂ (fun b => P b a) z := hloc
    choose! ι hι using hl
    have hc : ContinuousOn ι {w : ℂ | T < w.im} := fun w hw => by
      obtain ⟨P, hP⟩ := hι w hw
      refine (continuousAt_const.congr (f := fun _ => ι w) ?_).continuousWithinAt
      filter_upwards [hP, hop.mem_nhds hw] with z hz hz'
      obtain ⟨Q, hQ⟩ := hι z hz'
      exact F.disj _ _ _ _ hz.1.1 hQ.self_of_nhds.1.1 (hz.1.2.1.symm.trans hQ.self_of_nhds.1.2.1)
    have h0 : ι w₀ = k := by
      obtain ⟨Q, hQ⟩ := hι w₀ hw₀
      exact F.disj _ _ _ _ hQ.self_of_nhds.1.1 hP₀ (hQ.self_of_nhds.1.2.1.symm.trans hx₀)
    intro w hw
    have : ι w = k := (hcv.isPreconnected.constant hc hw hw₀).trans h0
    subst this
    exact hι w hw
  have hb : ∀ (U : Set ℂ) (s s' : ℂ → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen U → Convex ℝ U → U.Nonempty →
      (∀ z ∈ U, Adp F (y z) k (s z) ∧ ∀ a, DifferentiableAt ℂ (fun b => s b a) z) →
      (∀ z ∈ U, Adp F (y z) k (s' z) ∧ ∀ a, DifferentiableAt ℂ (fun b => s' b a) z) →
      ∃ δ : Lev (F.Di k) l, ∀ w ∈ U, ∀ a, s' w a = s w (δ.1 a) := fun U s s' h1 h2 h3 h4 h5 =>
    GlobalTheory.T.exists_const_substitution_of_holomorphic_families' _ (Lev (F.Di k) l) g (fun δ a => δ.1 a) U (fun w a => s w a) (fun w a => s' w a) h1 h2.isPreconnected h3
      (fun a z hz => ((h4 z hz).2 a).differentiableWithinAt) (fun a z hz => ((h5 z hz).2 a).differentiableWithinAt)
      fun w hw => (h4 w hw).1.exists_lev (h5 w hw).1
  obtain ⟨P, hP⟩ := GlobalTheory.T.germSections_halfPlane_global_section _ (fun w (s : ℂ → ((F.Di k).La →+ (Fin g → ℂ))) =>
      Adp F (y w) k (s w) ∧ ∀ a, DifferentiableAt ℂ (fun b => s b a) w) T
    (fun w s s' h h' => ⟨h.self_of_nhds ▸ h'.1, fun a =>
      (h'.2 a).congr_of_eventuallyEq (h.mono fun z hz => by simp only [hz])⟩) hidx
    (fun U s s' h1 h2 _ h4 h5 w hw h6 z hz => by
      obtain ⟨δ, hδ⟩ := hb U s s' h1 h2 ⟨w, hw⟩ h4 h5
      ext1 a
      rw [hδ z hz, (h4 w hw).1.1.2.1 ((hδ w hw a).symm.trans (by rw [h6]))])
    (fun U s s' _ _ _ h4 w hw h5 => by
      obtain ⟨δ, hδ⟩ := (h4 w hw).1.exists_lev h5.1
      exact ⟨fun z => (s z).comp δ.1.toLinearMap.toAddMonoidHom,
        fun z hz => ⟨(h4 z hz).1.comp δ, fun a => (h4 z hz).2 _⟩, AddMonoidHom.ext fun a => (hδ a).symm⟩)
  obtain ⟨δ, hδ⟩ := hb _ P (fun w => P (w + 1)) hop hcv ⟨w₀, hw₀⟩ hP fun z hz => by
    have hz' : T < (z + 1).im := by simpa using hz
    refine ⟨hper z ▸ (hP _ hz').1, fun a => ?_⟩
    exact DifferentiableAt.comp (g := fun b => P b a) (f := fun b => b + 1) z ((hP _ hz').2 a) (by fun_prop)
  exact ⟨P, δ, fun a z hz => ((hP z hz).2 a).differentiableWithinAt, fun w hw => ⟨(hP w hw).1, hδ w hw⟩⟩

end Adapted

theorem exists_pow_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (D : Datum H) {r : ℕ} (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (hef : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (δ : D.La ≃ₗ[𝓞 E] D.La) (hδ : ∀ a b, D.EF (δ a) (δ b) = D.EF a b) :
    ∃ M : ℕ, 0 < M ∧ ∃ γ ∈ X.Γ,
      ∀ a, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ ((δ ^ M) a) : Fin r → E) = (φ a : Fin r → E) := by
  let φ' : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype.comp φ.toLinearMap
  have hrange : Set.range φ' = X.Λ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      exact ⟨φ.symm ⟨y, hy⟩, by simp [φ']⟩
  have hspan : Submodule.span E (Set.range φ') = ⊤ := by rw [hrange]; exact X.Λ_span
  obtain ⟨γ, hγ⟩ := GlobalTheory.FrameFibre.exists_gl φ' (fun a b hab => φ.injective (Subtype.ext hab)) hspan δ
  have hn : ∀ (n : ℕ) a, ((γ ^ n : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ' a = φ' ((δ ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih => intro a; rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hγ, ih, pow_succ]; rfl
  have he : ∀ (n : ℕ) a b, D.EF ((δ ^ n) a) ((δ ^ n) b) = D.EF a b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih => intro a b; rw [pow_succ]; exact (ih _ _).trans (hδ a b)
  have hs : ∀ n : ℕ, ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ (γ ^ n) := fun n => by
    refine ⟨GlobalTheory.FrameFibre.herm_of_trace φ' hspan X.Gm _ (-X.ξ0) (neg_ne_zero.2 X.ξ0_ne) fun v w => ?_,
      fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · rw [hn, hn]
      exact (hef _ _).symm.trans ((congrArg _ (he n v w)).trans (hef _ _))
    · obtain ⟨v, rfl⟩ : y ∈ Set.range φ' := hrange ▸ hy
      rw [hn]
      exact (φ _).2
    · obtain ⟨v, hv⟩ : _ ∈ Set.range φ' := hrange.ge hy
      have : φ' ((δ ^ n).symm v) = y := by
        apply Matrix.mulVec_injective_of_isUnit (γ ^ n).isUnit
        rw [hn, LinearEquiv.apply_symm_apply, hv]
      rw [← this]
      exact (φ _).2
  obtain ⟨S, hS⟩ := X.Γ_index
  choose s hsS hs' using fun n => hS _ (hs n)
  have key : ∀ n m, n < m → s n = s m → ∃ M : ℕ, 0 < M ∧ ∃ γ ∈ X.Γ,
      ∀ a, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ ((δ ^ M) a) : Fin r → E) = (φ a : Fin r → E) := by
    intro n m h e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨d + 1, d.succ_pos, (γ ^ (d + 1))⁻¹, ?_, fun a => ?_⟩
    · have := mul_mem (inv_mem (hs' (n + d + 1))) (hs' n)
      rw [e] at this
      convert this using 1
      group
    · change _ *ᵥ φ' _ = φ' a
      rw [← hn, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨n, m, hne, e⟩ := Finite.exists_ne_map_eq_of_infinite fun n => (⟨s n, hsS n⟩ : S)
  rcases hne.lt_or_gt with h | h
  · exact key n m h (congrArg Subtype.val e)
  · exact key m n h (congrArg Subtype.val e).symm

theorem exists_halfPlane {r : ℝ} (hr : 0 < r) : ∃ T : ℝ, ∀ w : ℂ, T < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r := by
  refine ⟨-Real.log r / (2 * Real.pi), fun w hw => ?_⟩
  rw [div_lt_iff₀ (by positivity)] at hw
  rw [mem_ball_zero_iff, eTwoPi, Complex.norm_exp, ← Real.lt_log_iff_exp_lt hr]
  simp
  linarith

set_option maxHeartbeats 1000000 in

theorem exists_orbit_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∃ (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), (∀ w : ℂ, T < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r) ∧ IsOrbit (U.X k) T M γ xx ∧ IsLift U k y T xx := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y hσ hU harc hm
  have hσ' : Formalism.L2.PjFree.GoodEmb c σ := hσ
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨hr, hX, hcov, -, -, g, e, F, ik, φL, hEF, hpt⟩ := hU'
  obtain ⟨T, hT⟩ := exists_halfPlane harc.1.1
  have hed : Differentiable ℂ eTwoPi := by unfold eTwoPi; fun_prop
  have he1 : ∀ w, eTwoPi (w + 1) = eTwoPi w := fun w => by
    rw [eTwoPi, eTwoPi, mul_add, Complex.exp_add, mul_one, Complex.exp_two_pi_mul_I, mul_one]
  have hw₀ : T < (((T + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  obtain ⟨k, x₀, t, hx₀⟩ := hcov (y (eTwoPi (((T + 1 : ℝ) : ℂ) * Complex.I)))
  obtain ⟨P₀, hP₀e, hP₀, hu₀, -⟩ := hpt k x₀
  obtain ⟨P, δ, hPd, hP⟩ := exists_adp_global F (fun w => y (eTwoPi w)) T (fun w => by rw [he1]) (fun w hw => by
    obtain ⟨R, _, xR, vR, ev, V, hV, hwV, hev, hy⟩ := GlobalTheory.T.arc_off_boundary_descends_to_moduli_localization E H Dw l Xo c O β Z σ A φ x fr ψ r y harc hm
      (eTwoPi w) (hT w hw) (Complex.exp_ne_zero _)
    obtain ⟨B', k, P, hB', hb, hPd, hP⟩ := exists_adp_local F xR vR (m := 1) (fun b => ev (b 0))
      (B := (fun b => b 0) ⁻¹' V) (fun b => y (b 0)) (hV.preimage (continuous_apply 0))
      (fun t => (hev t).comp (differentiable_apply 0).differentiableOn fun _ h => h) (fun b hb => hy _ hb)
      (b₀ := fun _ => eTwoPi w) hwV
    have hd : Differentiable ℂ fun (z : ℂ) (_ : Fin 1) => eTwoPi z := differentiable_pi.2 fun _ => hed
    refine ⟨k, fun z => P fun _ => eTwoPi z, ?_⟩
    filter_upwards [(hB'.preimage hd.continuous).mem_nhds hb] with z hz
    exact ⟨hP _ hz, fun a => DifferentiableAt.comp (g := fun b => P b a) (f := fun (z : ℂ) (_ : Fin 1) => eTwoPi z) z
      ((hPd a).differentiableAt (hB'.mem_nhds hz)) (hd z)⟩) (ik k) hw₀ hP₀
    (hx₀.1.trans hu₀)
  obtain ⟨idx, hper, -, honto⟩ := GlobalTheory.GenericFrames.dictionary c σ e (F.Di (ik k)) (U.X k) (φL k) hσ' (F.sig _).1
    (F.sig _).2 hr (hX k).1 (hX k).2 (hEF k)
    (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ N (U.X k) (φL k) hσ' hr (hX k).1 (hX k).2 (hEF k) x₀.1 x₀.2
      P₀ hP₀e hP₀)
  have hall : ∀ {p : (Fin N → E) → (U.X k).Ψ → Fin N → Prop},
      (∀ a j, p (φL k a : Fin N → E) (idx j).1 (idx j).2) → ∀ v ∈ (U.X k).Λ, ∀ τ i, p v τ i := by
    intro p h v hv τ i
    obtain ⟨a, rfl⟩ : ∃ a, (φL k a : Fin N → E) = v := ⟨(φL k).symm ⟨v, hv⟩, by simp⟩
    obtain ⟨j, hj⟩ := idx.surjective (τ, i)
    obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
    exact h a j
  haveI : Inhabited (Frame (U.X k).Ψ N) := inferInstance
  choose! x₁ hx₁ hr₁ using fun (w : ℂ) (hw : T < w.im) => honto (P w) (hP w hw).1.1
  obtain ⟨xx, hxd, hxx⟩ := GlobalTheory.T.exists_holomorphicFrames_same_periodCoordinates E N (U.X k) {w : ℂ | T < w.im} x₁ hx₁
    (hall fun a j => (differentiableOn_pi.1 (hPd a) j).congr fun w hw => hr₁ w hw a j)
  have hxP : ∀ w : ℂ, T < w.im → ∀ a j,
      GlobalTheory.GenericFrames.pc (U.X k) (xx w) (φL k a : Fin N → E) (idx j).1 (idx j).2 = P w a j :=
    fun w hw a j => ((hxx w hw).2 _ _ _).trans (hr₁ w hw a j)
  obtain ⟨M, hM, γ, hγ, hγe⟩ := exists_pow_mem (F.Di (ik k)) (U.X k) (φL k) (hEF k) δ.1 δ.2.1
  have hsh : ∀ (n : ℕ) (w : ℂ), T < w.im → ∀ a, P (w + n) a = P w ((δ.1 ^ n) a) := by
    intro n w hw
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Nat.cast_succ, ← add_assoc, (hP _ (by simpa using hw)).2, ih, pow_succ]
      rfl
  refine ⟨k, T, M, γ, xx, hT, ⟨hM, hγ, hxd, fun w hw => (hxx w hw).1, fun w hw => ?_⟩,
    fun w hw => ⟨(hxx w hw).1, ?_⟩⟩
  · have hw' : T < (w + M).im := by simpa using hw
    refine GlobalTheory.T.exists_unipotentTriangular_of_periodCoordinates_eq E N (U.X k) _ _ (dom_lact _ (hxx w hw).1 ((U.X k).Γ_stab γ hγ)) (hxx _ hw').1
      (hall fun a j => ?_)
    rw [hxP _ hw', hsh M w hw, ← hxP w hw, ← hper, ← hper,
      ← GlobalTheory.CongrOrbit.perFr_lact _ _ γ ((U.X k).Γ_stab γ hγ).1]
    exact congrArg (fun v => Formalism.L2.PjFree.perFr (U.X k) (lact γ (xx w)) v _ _) (hγe a)
  · obtain ⟨Q, hQe, hQ, hu, hd, -⟩ := hpt k ⟨xx w, (hxx w hw).1⟩
    have : Q = P w := by
      ext a j
      exact (hQe a j).trans ((hper _ _ j).trans (hxP w hw a j))
    subst this
    exact Adp.sameLie (F := F) ⟨hQ, hu, hd⟩ (hP w hw).1

end GlobalTheory.ShFam.ArcLift
