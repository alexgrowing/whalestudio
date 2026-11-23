import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem linearIndependent_symm_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : T) :
    LinearIndependent ℂ (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) := by
  have hinj : Function.Injective fun i : Fin (m τ) => e.symm ⟨τ, i⟩ :=
    e.symm.injective.comp sigma_mk_injective
  have := ((Pi.basisFun ℂ (Fin g)).linearIndependent.comp _ hinj).map' L.symm.toLinearMap L.symm.ker
  have hf : (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) =
      L.symm.toLinearMap ∘ ((Pi.basisFun ℂ (Fin g)) ∘ fun i : Fin (m τ) => e.symm ⟨τ, i⟩) := by
    funext i
    simp
  rw [hf]
  exact this

theorem point_exp_eq_of_isometry_levels (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La)
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hpq : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA' : ∀ a, ∃ x, gm (Fu.t i a) = Fu.t i' a + l.A • x)
    (hP : IsPeriod (Fu.Di i) ty P) (hP' : IsPeriod (Fu.Di i') ty P')
    (hiso : ∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e)
    (hL : ∀ u, P' (gm u) = L (P u)) : Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  have hu : Fu.u i P = Fu.u i' P' :=
    (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hσ hty (Fu.Di i) (Fu.Di i')
      (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.ex_diff i P hP).1, (Fu.ex_diff i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.ex_diff i' P' hP').1, (Fu.ex_diff i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP',
        Fu.ex_weil i' P' hP', Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ⟨gm, L, hiso, hM, hA', hL⟩
  obtain rfl : i = i' := Fu.disj i i' P P' hP hP' hu
  letI : StarRing (𝓞 E) := H.starRing
  exact GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hM hA' hL

theorem flowTie_of_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hY hLM hLA O _ β Y χ W Ha
  have hK : Known := GlobalTheory.ArcCM.known_holds
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ :=
    GlobalTheory.ArcCompare.holArc_agrees hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w₁ at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s₁, hs₁, h, hh⟩ := o4 w₁ hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hg1 : ∀ v, g₁ (gm.symm v) = gam v := fun v => by rw [← hgm, gm.apply_symm_apply]
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hEF' : ∀ u v, (Uw.F.Di (Uw.ik k)).EF u v = (Uw.F.Di Ha.i).EF (gm.symm u) (gm.symm v) := fun u v => by
    rw [← hEF, gm.apply_symm_apply, gm.apply_symm_apply]
  have hP : ∀ u, Uw.Pm k ⟨_, hs₁⟩ (gm u) = L (Ha.Pw w₁ u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w₁ u).symm.trans (h.apply_symm_apply _).symm
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have h0 : ∀ v, h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := fun v => by
    have := e3 0 (Uw.F.t Ha.i v)
    rw [Ha.Pw_eq, zero_smul, add_zero] at this
    exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLM v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add, map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  have hlevA : ∀ v, ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.A • e := by
    intro v
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelA v
    have hq : q = Λ.toGtDict.qk l.A (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.etaA v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.etaA v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLA v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add, map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨-, p2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w₁) (Uw.Pm k ⟨_, hs₁⟩) gm L hpq
    hσ hty hlevA (Ha.period w₁ hw1) (Uw.period k _) hEF hlev hP
  obtain ⟨nn, n1, n2, n3, n4, n5, n6⟩ :=
    GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y (aC.restrict β) χ W _ _ Uw.F Ha
  have hlin : ∀ w w' v, Ha.Pw w v = Ha.Pw w' v + (w - w') • Ha.Pw w' (nn v) := by
    intro w w' v
    rw [Ha.Pw_eq, Ha.Pw_eq, Ha.Pw_eq, n1 (nn v), n4 _ (n3 v), map_zero, smul_zero, add_zero, ← n1, sub_smul]
    abel
  have hyg : ∀ u, Ha.y u = Λ.eX (g₁ u).y := fun u => (e2 u).symm
  let nn' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La :=
    gm.toLinearMap ∘ₗ nn ∘ₗ gm.symm.toLinearMap
  have hnn'e : ∀ v, gm.symm (nn' v) = nn (gm.symm v) := fun v => gm.symm_apply_apply _
  let y'' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Λ.A.X := Λ.A.yLin ∘ₗ gam.toLinearMap
  have hy'' : Function.Surjective y'' := Λ.A.yLin_surjective.comp gam.surjective
  have hnn'' : ∀ v v', -(Uw.F.Di (Uw.ik k)).EF (nn' v) v' = Λ.A.be (y'' v) (y'' v') := by
    intro v v'
    rw [hEF', hnn'e, n2, hyg, hyg, hg1, hg1]
    exact Λ.be_eq _ _
  have hrep'' : ∀ η : Module.Dual ℤ Λ.A.X, ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = η (y'' v) := by
    intro η
    obtain ⟨t, ht, -⟩ := n6 (η.toAddMonoidHom.comp Λ.eX.symm.toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨gm t, fun v => ?_⟩
    rw [hEF', gm.symm_apply_apply, ht, hyg, hg1]
    show η (Λ.eX.symm (Λ.eX _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hyt : y'' t' = 0 := by
    have hy0 := n5 (gm.symm t') fun v' hv' => by
      have h3 := o3 (gm v')
      have h4 : (g₁ v').y = 0 := (map_eq_zero_iff _ Λ.eX.injective).1 (by rw [← hyg]; exact hv')
      rw [hgm, h4, map_zero] at h3
      rw [← hEF, gm.apply_symm_apply]
      exact neg_eq_zero.1 h3
    rw [hyg, hg1] at hy0
    exact (map_eq_zero_iff _ Λ.eX.injective).1 hy0
  let x₀ : (U.X k).dom := ⟨_, hs₁⟩
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₀
  have hκ := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x₀ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, -, hbe, hsp, -, hform⟩ := GlobalTheory.ArcFlow.rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y'' hY hκ hy''
    Λ.A.be Λ.A.be_symm Λ.A.be_pos nn' hnn'' hrep'' ξ hξ0 t' o3 hyt
  have hform' : ∀ v, (Uw.φ k (nn' v) : Fin r → E) =
      (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ' := fun v => by
    rw [hform v, o2]
  have hξ'0 : herm (U.X k).Gm ξ' ξ' = 0 := hξ.2.1
  have hLs : ∀ z, (Uw.F.ex Ha.i (Ha.Pw w₁) (L.symm z)).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x₀) z).left := fun z => by
    rw [← p2 (L.symm z), L.apply_symm_apply]
  refine ⟨Ha.T, fun τ => s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ), fun τ => (τ.1 sE).re,
    fun τ i => L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1), fun τ => hsp τ.1, fun τ => ⟨?_, fun i jj hij => ?_⟩,
    fun w hw => ?_⟩
  · exact linearIndependent_symm_single Uw.e L τ
  · refine GlobalTheory.DerivativeDetermination.type_map Uw.e Uw.F (Uw.period k x₀) (Ha.period w₁ hw1) L.symm.toLinearMap hLs τ _
      (fun j hj => ?_) jj hij
    by_cases hjj : j = Uw.e.symm ⟨τ, i⟩
    · subst hjj; simp
    · exact absurd (Pi.single_eq_of_ne hjj _) hj
  · let Pw' : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      L.toLinearMap.toAddMonoidHom.comp ((Ha.Pw w).comp gm.symm.toLinearMap.toAddMonoidHom)
    have hg' : ∀ a b, (Uw.F.Di Ha.i).EF (gm.symm a) (gm.symm b) = (Uw.F.Di (Uw.ik k)).EF a b :=
      fun a b => (hEF' a b).symm
    have hPer : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) Pw' := by
      have := GlobalTheory.UnifCompare.isPeriod_move
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w₁ hw1)) (Uw.period k x₀)
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w hw)) (LinearEquiv.refl _ _) L
        (fun _ _ => rfl) (fun a => by
          show Uw.Pm k x₀ a = L (Ha.Pw w₁ (gm.symm a))
          rw [← hP, gm.apply_symm_apply])
      exact this
    have hPx : ∀ v, Pw' v = Uw.Pm k x₀ v + (w - w₁) • Uw.Pm k x₀ (nn' v) := by
      intro v
      have a1 := hP (gm.symm v)
      rw [gm.apply_symm_apply] at a1
      have a2 := hP (nn (gm.symm v))
      show L (Ha.Pw w (gm.symm v)) = _
      rw [hlin w w₁, map_add, map_smul, ← a1, ← a2]
      rfl
    obtain ⟨hxw, hPw'⟩ := GlobalTheory.ArcFlow.flow_period Uw hσ hU k hκ nn' ξ' hξ'0 sE hbe.1 hform' x₀ (w - w₁) Pw' hPer hPx
    have heq : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x₀.1 =
        (U.X k).flow ξ' (fun τ => (s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ)) + w * (((τ.1 sE).re : ℝ) : ℂ)) x := by
      rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow (U.X k) hξ'0]
      congr 1
      funext τ
      simp only [Pi.add_apply]
      ring
    obtain ⟨q1, q2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hxw⟩) gm L
      hpq hσ hty hlevA (Ha.period w hw) (Uw.period k _) hEF hlev (fun u => by
        rw [hPw']
        show L (Ha.Pw w (gm.symm (gm u))) = _
        rw [gm.symm_apply_apply])
    refine ⟨heq ▸ hxw, ?_⟩
    have hpt : (⟨_, heq ▸ hxw⟩ : (U.X k).dom) = ⟨_, hxw⟩ := Subtype.ext heq.symm
    rw [hpt]
    have hlie := Uw.lie k ⟨_, hxw⟩
    refine ⟨hlie.1.trans q1.symm, fun τ i => ?_⟩
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F Ha.i (Ha.Pw w) (Ha.period w hw) (Uw.ik k)
      (Uw.Pm k ⟨_, hxw⟩) L.toLinearMap (Uw.period k _) q2 _ _).2 ?_
    rw [show L.toLinearMap (L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1)) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 from
      L.apply_symm_apply _]
    exact hlie.2 τ i

end GlobalTheory.CuspFrom
