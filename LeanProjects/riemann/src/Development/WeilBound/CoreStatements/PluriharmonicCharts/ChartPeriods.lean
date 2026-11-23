import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenDet
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryDiscMapEmbeddingFixed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinates
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocallyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem eig_coords {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {P : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left} (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v) (a : 𝓞 E) (cc : ℂ)
    (h : v ≫ (Xo.univ.t.act.act a).left = spMap (Tor.epsMul cc) ≫ v) (j : Fin g) : ty j (a : E) * w j = cc * w j := by
  obtain ⟨v₁, hv₁, -⟩ := (FU.ex_diff i P hP).1 (PullbackSections.ExpRows.tyD ty a w)
  have h1 := PullbackSections.ExpRows.isDerivAt0_comp_lin (PullbackSections.anHol FU i P hP) (PullbackSections.ExpRows.tyD ty a) hv₁
  have h2 := PullbackSections.ExpRows.isDerivAt0_comp_hom hv (Xo.univ.t.act.act a).left
  have hfun : (fun z => (FU.ex i P z).left ≫ (Xo.univ.t.act.act a).left) =
      fun z => (FU.ex i P (PullbackSections.ExpRows.tyD ty a z)).left := funext fun z => by
    rw [PullbackSections.ExpRows.tyD_apply, FU.ex_lin i P hP a z]
    rfl
  rw [hfun] at h2
  have h3 := PullbackSections.ExpRows.isDerivAt0_unique h1 h2
  have h4 := PullbackSections.ExpRows.isDerivAt0_smul hv cc
  rw [← h, ← h3] at h4
  exact congrFun (((FU.ex_diff i P hP).2 v₁ hv₁.1).unique hv₁ h4) j

theorem chart_periods {Xo : Moduli D l} {σ : KA l →+* ℂ} {n : ℕ} (C : BdryChart Xo σ n 0) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) {A : Type} (x : A → Fin C.g → C.R) :
    ∃ (i : Fin FU.n) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
      (W : A → (Fin n → ℂ) → Fin g → ℂ) (G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ),
      IsOpen B ∧ 0 ∈ B ∧ B ⊆ Metric.ball 0 1 ∧ IsHolPeriods (FU.Di i) ty B P ∧
      (∀ a, DifferentiableOn ℂ (W a) B) ∧ ∀ u ∈ B, FU.u i (P u) = C.pt u ≫ C.k ∧
        ((G u).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (G u) z z).re) ∧
          ∀ x y, (hermForm (G u) (P u x) (P u y)).im = (FU.Di i).EF x y) ∧
        (∃ Hm, C.IsRiem u Hm ∧ ∀ a b, hermForm Hm (fun e => C.ψ u (x a e)) (fun e => C.ψ u (x b e)) =
          hermForm (G u) (W a u) (W b u)) ∧
        ∀ a (t : 𝓞 E) (cc : ℂ), (spMap (dualMap (C.ψ u)) ≫ (C.M.pt (x a)).left) ≫ (C.t.act.act t).left =
          spMap (Tor.epsMul cc) ≫ spMap (dualMap (C.ψ u)) ≫ (C.M.pt (x a)).left →
          ∀ j, ty j (t : E) * W a u j = cc * W a u j := by
  classical
  have hpu : ∀ ρ : ℝ, punct n 0 ρ = Metric.ball 0 ρ := fun ρ => by ext z; simp [punct]
  obtain ⟨ρ, hρ0, hρB, ⟨e⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ C.t.semi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have hy : IsHolTo (Metric.ball 0 ρ) fun u => C.pt u ≫ C.k :=
    GlobalTheory.LocLift.isHolTo_comp_hom (Marking.isHolTo_mono' (Marking.isHolTo_pt C)
      (by rw [hpu]; exact hρB) Metric.isOpen_ball) C.k
  obtain ⟨B', i, P₀, hB, h0, hsubB, hP, hu⟩ := FU.lift n (Metric.ball 0 ρ) _ Metric.isOpen_ball
    (fun b hb => by rw [Category.assoc]; exact (C.pt_eq b (by rw [hpu]; exact hρB hb)).2) hy 0
    (Metric.mem_ball_self hρ0)
  have hsub1 : B' ⊆ punct n 0 1 := by rw [hpu]; exact hsubB.trans hρB
  obtain ⟨r, Wt, hr⟩ := Marking.exists_family C FU i P₀ hsub1 hP hu ((1 : Over.mk (C.pt 0) ⟶ C.tV.G).left)
  have hol := Marking.family_hol C FU i P₀ hB hsub1 hP Wt
    (fun b hb x => ⟨((hr b hb).2.2.2.1 x).1, ((hr b hb).2.2.2.1 x).2.1⟩)
  have holr : IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (r bz.1 bz.2).left) :=
    GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_comp hol C.m₁.φ)
      fun bz hb => (((hr _ hb.1).2.2.2.1 _).2.2).symm
  obtain ⟨hl, hlhol, hl2⟩ := exists_linear_lift_of_additive_family C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e g B' r
    hB hsubB (fun b hb => (hr b hb).1) holr
  have hbij : ∀ z ∈ B', Function.Bijective (hl z) := by
    intro z hz
    obtain ⟨hadd, hons, hker, -, -⟩ := hr z hz
    obtain ⟨δ, hδ, hiso⟩ := Marking.isolated_of_isPeriod _ (hP.1 z hz)
    refine Marking.bijective_of_exp (e.ex z) (r z) (hl z) (e.add z (hsubB hz)) (hl2 z hz).1 hons
      ⟨δ, hδ, fun x hx h1 => hiso x hx ((hker x).1 h1)⟩ ?_
    obtain ⟨W, hW, hzW, ρ', hρ', hinj⟩ := ExpLift.ex_inj_near e (hsubB hz)
    refine ⟨ρ', hρ', fun y hy h1 => hinj z hzW y (mem_ball_zero_iff.2 hy) 0 (Metric.mem_ball_self hρ') ?_⟩
    rw [h1, ExpLift.ex_zero e (hsubB hz)]
  have hg : g = C.g := by simpa using (LinearEquiv.ofBijective (hl 0) (hbij 0 h0)).finrank_eq
  subst hg
  let hm : (Fin n → ℂ) → Matrix (Fin C.g) (Fin C.g) ℂ := fun z => LinearMap.toMatrix' (hl z)
  have hmh : HolM B' hm := fun a b => differentiableOn_pi.1 (hlhol (Pi.single b 1)) a
  have hmv : ∀ z y, hm z *ᵥ y = hl z y := fun z y => LinearMap.toMatrix'_mulVec _ _
  have hmd : ∀ z ∈ B', (hm z).det ≠ 0 := fun z hz h => by
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hy0 ((hbij z hz).1 (by rw [← hmv, hy, map_zero]))
  let W : A → (Fin n → ℂ) → Fin C.g → ℂ := fun a z => (hm z)⁻¹ *ᵥ fun e => C.ψ z (x a e)
  have hW : ∀ z ∈ B', ∀ a, hl z (W a z) = fun e => C.ψ z (x a e) := fun z hz a => by
    rw [← hmv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (hmd z hz)), Matrix.one_mulVec]
  choose! G hG using fun z (hz : z ∈ B') => (hP.1 z hz).2.2.2.2
  refine ⟨i, B', P₀, W, G, hB, h0, hsubB.trans hρB, hP, fun a => differentiableOn_pi.2 fun j => ?_,
    fun z hz => ⟨hu z hz, hG z hz, ?_, fun a t cc hc => ?_⟩⟩
  · simp only [W, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun k _ => (hmh.inv hmd j k).mul ((C.hol.2 _).mono (hsubB.trans hρB))
  · obtain ⟨-, -, -, hWz, -⟩ := hr z hz
    let hh : (Fin C.g → ℂ) ≃ₗ[ℂ] (Fin C.g → ℂ) := LinearEquiv.ofBijective (hl z) (hbij z hz)
    obtain ⟨Hm, -, hf⟩ := Marking.herm_transport (G z) hh (hG z hz).1
    refine ⟨Hm, Marking.isRiem_of_period C FU e i (hsubB hz) (hsub1 hz) (P₀ z) (hP.1 z hz) (hu z hz) (r z) (Wt z)
        (fun x => ⟨(hWz x).2.1, (hWz x).2.2⟩) hh (hl2 z hz).2.2 (G z) Hm (hG z hz).1 (hG z hz).2.2 hf, fun a b => ?_⟩
    rw [← hf, ← hW z hz, ← hW z hz]
    rfl
  · obtain ⟨-, -, -, hWz, -⟩ := hr z hz
    have hD : IsDerivAt0 (fun x => (r z x).left) (W a z) (spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x a)).left) := by
      rw [(hl2 z hz).2.2, hW z hz]
      exact Marking.isDerivAt0_frame e (hsubB hz) (x a)
    haveI := C.j_open
    haveI : IsOpenImmersion C.m₁.φ := MorphismProperty.of_isPullback C.m₁.cart.1.flip ‹IsOpenImmersion C.j›
    obtain ⟨v', hv1, hv2⟩ := Marking.deriv_of_open C.m₁.φ (Wt z) (W a z) _ (by
      have : (fun x => Wt z x ≫ C.m₁.φ) = fun x => (r z x).left := funext fun x => (hWz x).2.2
      rw [this]; exact hD)
    have h1 := PullbackSections.ExpRows.isDerivAt0_comp_hom hv2 C.m₂.φ
    have h2 : (fun x => Wt z x ≫ C.m₂.φ) = fun x => (FU.ex i (P₀ z) x).left := funext fun x => (hWz x).2.1
    rw [h2] at h1
    have h3 : v' ≫ (C.tV.act.act t).left = spMap (Tor.epsMul cc) ≫ v' := by
      rw [← cancel_mono C.m₁.φ, Category.assoc, Category.assoc, hv1, ← hc, ← hv1, Category.assoc]
      exact congrArg (v' ≫ ·) (C.m₁.act t)
    refine eig_coords FU i (hP.1 z hz) h1 t cc ?_
    rw [← Category.assoc, ← h3, Category.assoc, Category.assoc]
    exact congrArg (v' ≫ ·) (C.m₂.act t).symm

theorem exists_chart {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0})
    (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hs : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)))
    (hpt : ∀ u ∈ Flat.punct n 0 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)),
      x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) :
    ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n 0) (h : Sp C.R ⟶ X')
      (κ : C.V ⟶ Xo.XF c), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ κ ≫ Y.j = C.j ≫ h ≫ jx ∧
      κ ≫ pullback.fst _ _ = C.k ∧
      ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  classical
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let fP := pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let sZ := pullback.snd jx fP
  let fZ := pullback.fst jx fP
  let j := pullback.fst sZ Y.jQ
  let g := pullback.snd sZ Y.jQ
  have := Y.jQ_open
  have hj : IsOpenImmersion j := inferInstance
  let k : pullback sZ Y.jQ ⟶ Xo.X := g ≫ pullback.fst _ _

  obtain ⟨tZ, ⟨mZ⟩⟩ := exists_sab fZ t
  obtain ⟨tU, ⟨mU⟩⟩ := exists_sab g Y.oF.t
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mZ
  obtain ⟨q₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m mU
  have e₁ : g ≫ Y.jQ ≫ fP = j ≫ fZ ≫ jx := by
    have a₁ : j ≫ sZ = g ≫ Y.jQ := pullback.condition
    have a₂ : fZ ≫ jx = sZ ≫ fP := pullback.condition
    rw [a₂, ← Category.assoc g, ← a₁, Category.assoc]
  rw [e₁] at q₂
  have q₁' : SABMap tZ Y.t (fZ ≫ jx) := q₁
  obtain ⟨mj, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel q₁' q₂
  obtain ⟨mk, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap mU

  let p' : (Fin n → ℂ) → (Sp ℂ ⟶ X') := fun u => if u ∈ Metric.ball (0 : Fin n → ℂ) 1 then p u else p 0
  have hp'e : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u = p u := fun u hu => if_pos hu
  have hp' : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) p' := GlobalTheory.LocLift.isHolTo_congr hp hp'e
  have hs' : ∀ u, (p' u ≫ jx) ≫ Y.s = spMap τ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun u => by
    have : p' u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) := by
      by_cases hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1
      · rw [hp'e u hu]; exact hs u hu
      · simp only [p', if_neg hu]; simpa [h0] using hs 0 h0
    rw [Category.assoc, this]
    simp [spMap]
  let q : (Fin n → ℂ) → (Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    fun u => pullback.lift (p' u ≫ jx) (spMap τ) (hs' u)
  have hq : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) n _ _ _ hs' Metric.isOpen_ball
      (GlobalTheory.LocLift.isHolTo_comp_hom hp' jx) (GlobalTheory.PeriodTests.isHolTo_const Metric.isOpen_ball _)
  have hc : ∀ u, p' u ≫ jx = q u ≫ fP := fun u => (pullback.lift_fst _ _ _).symm
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback jx fP) := fun u => pullback.lift (p' u) (q u) (hc u)
  have hy : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) y :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ jx fP n _ _ _ hc Metric.isOpen_ball hp' hq
  have hpu : ∀ z ∈ Flat.punct n 0 1, ∃ w : Sp ℂ ⟶ pullback sZ Y.jQ, w ≫ j = y z ∧
      w ≫ k ≫ Xo.s = spMap (τ.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    have hr : Set.range (q z) ⊆ Set.range Y.jQ :=
      hpt z hz (q z) ((pullback.lift_fst _ _ _).trans (by rw [hp'e z hz.1]))
    let w₀ := IsOpenImmersion.lift Y.jQ (q z) hr
    have hw₀ : w₀ ≫ Y.jQ = q z := IsOpenImmersion.lift_fac _ _ _
    have hys : y z ≫ sZ = w₀ ≫ Y.jQ := (pullback.lift_snd _ _ _).trans hw₀.symm
    refine ⟨pullback.lift (y z) w₀ hys, pullback.lift_fst _ _ _, ?_⟩
    have h₁ : pullback.lift (y z) w₀ hys ≫ k = w₀ ≫ pullback.fst _ _ := by
      simp only [k, g]; rw [pullback.lift_snd_assoc]
    rw [← Category.assoc, h₁, Category.assoc, pullback.condition, ← Category.assoc]
    have h₂ : w₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap τ := by
      rw [← Y.jQ_over, ← Category.assoc, hw₀]
      exact pullback.lift_snd _ _ _
    rw [h₂]
    simp [spMap]
  obtain ⟨ρ, C, i, e, hρ, hρ1, -, ⟨mi⟩, hej, hek, hψ⟩ :=
    Flat.exists_bdryChart_of_hol E H D l Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) _ tZ _ j k tU n 0 y
      (Nat.zero_le _) hj ⟨mj⟩ ⟨mk⟩ hy hpu
  obtain ⟨mh, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mZ mi
  refine ⟨ρ, C, i ≫ fZ, e ≫ g, hρ, hρ1, ⟨mh⟩, ?_, (Category.assoc _ _ _).trans hek, fun z hz => ?_⟩
  · have e₂ : g ≫ Y.j = j ≫ fZ ≫ jx := e₁
    rw [Category.assoc, e₂, ← Category.assoc, hej, Category.assoc, Category.assoc]
  have hin : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  rw [← Category.assoc, hψ z hz, ← hp'e _ hin]
  exact pullback.lift_fst _ _ _

end PositivityTheory.Xgp.c_bm_exists_period
