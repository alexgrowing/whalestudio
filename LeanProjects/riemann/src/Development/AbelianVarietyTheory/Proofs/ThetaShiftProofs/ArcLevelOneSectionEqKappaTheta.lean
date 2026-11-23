import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibreStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsThetaStatement

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem eq_at_zero_of_eq_off_zeros {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F p q : V → ℂ}
    (hF : Continuous F) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) {v₀ : V} (h₀ : F v₀ ≠ 0)
    (h : ∀ v, F v ≠ 0 → p v = q v) : p 0 = q 0 := by
  have hl : Differentiable ℂ fun t : ℂ => t • v₀ := differentiable_id.smul_const _
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => p (t • v₀)) Set.univ := fun t _ => (hp.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => q (t • v₀)) Set.univ := fun t _ => (hq.comp hl).analyticAt t
  have h3 : ∀ᶠ t in nhds (1 : ℂ), F (t • v₀) ≠ 0 :=
    (hF.comp hl.continuous).continuousAt.eventually_ne (by simpa using h₀)
  have h4 := AnalyticOnNhd.eq_of_eventuallyEq h1 h2 (h3.mono fun t ht => h _ ht)
  simpa using congrFun h4 0

theorem isFnInRigFrame_of_isFn {D₀ : Out.DegPre ℂ} {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) (hr : u.IsRig D₀.rig)
    {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ} (hθ : u.IsFn th θ) {p : (Fin g → ℂ) → (Fin n → ℂ)}
    (hp : Differentiable ℂ p) (hp0 : p 0 = 0) {Q ϑ : (Fin g → ℂ) → ℂ} (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 0)
    (h : ∀ z, θ (p z) = Complex.exp (Q z) * ϑ z) :
    IsFnInRigFrame D₀ (fun z => (u.ex (p z)).left) th ϑ := by
  refine ⟨fun j z => Complex.exp (Q z) * u.fr j (p z), fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hj => ?_, fun j z hz => ?_⟩
  · exact hQ.cexp.differentiableOn.mul ((u.fr_hol j).comp hp.differentiableOn fun z hz => hz)
  · exact mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne j _ hz)
  · beta_reduce
    rw [u.fr_compat j j' _ hz]
    ring
  · have e1 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
    have e2 : (u.ex 0).left = eSec D₀.P.A := by
      rw [e1, Hom.one_def, toUnit_unit, Category.id_comp]
      rfl
    beta_reduce at hj ⊢
    rw [hp0, e2] at hj
    rw [hQ0, hp0, Complex.exp_zero, _root_.one_mul]
    exact hr (fun _ => j) fun x hx => Set.mem_iInter.2 fun _ => hj hx
  · beta_reduce
    rw [hθ j _ hz, h]
    ring

set_option maxHeartbeats 800000 in

theorem arc_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  obtain ⟨T₀, hT⟩ := Λ.A.exists_isConvLine
  refine ⟨max T₀ (max T₁ K.T), fun T hTT th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ hth hEF hS hP hc₁ hc₂ r₂ r₁ r₀ hex => ?_⟩
  have hT0 : T₀ ≤ T := (le_max_left _ _).trans hTT
  have hT1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTT
  have hTK : K.T ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hTT
  obtain ⟨θ, hθ, hθ0, hfn⟩ := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.2 th hth.1
  let bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ.A.La := bas.trans (K.gam.toAddEquiv.toIntLinearEquiv)
  have hb : ∀ u, bas' u = K.gam (bas u) := fun _ => rfl
  obtain ⟨hu, hτ, d₁, d₂, -, -, hdS, ⟨Q, κ, -, hQ, hQ0, hκ, hSum, hoff⟩, huniq⟩ :=
    Λ.A.theta_comparison hT K.h.toLinearEquiv hθ hθ0 bas' (fun u v => by rw [hb, hb, K.EF_eq, hEF]) S
      (fun u => by rw [← hS, hb, map_eq_zero_iff _ Λ.ε.injective]) h τ
      (fun w k => by simpa only [hb, K.Pw_eq, ContinuousLinearEquiv.coe_toLinearEquiv] using hP w k)
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv] at hSum hoff huniq
  have hSne : ∀ w : ℂ, T₀ < w.im → ∃ v, Λ.A.Sum 1 0 θ w v ≠ 0 := fun w hw => by
    obtain ⟨v, hv⟩ := Λ.A.exists_Sum_ne_zero one_ne_zero 0 hθ0 fun z =>
      AnArc.summable_term hT one_ne_zero hθ hw (0, z)
    exact ⟨_, hv⟩
  have key : ∀ w : ℂ, T < w.im → ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w))
      (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr →
      ∃ (lam : ℂ) (f : Λ.A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧
        (∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (K.h v) = f v * Ψ.fr w j v) ∧
        ∀ v, Λ.A.Sum 1 0 θ w v = lam * thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) * f v := by
    intro w hw fr hfr
    have hw0 := hT0.trans_lt hw
    have tr : ∀ (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) ϑ, y = y' →
        IsThetaFrameAt Xo.univ.t.PP y e ϑ fr → IsThetaFrameAt Xo.univ.t.PP y' e ϑ fr := by
      rintro y _ e ϑ rfl h
      exact h
    refine GlobalTheory.T.two_rigidified_theta_frames_on_fibre hL hL2 E H D l Xo Λ.A lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) g K.h _ _ fr
      (hfib w (hT1.trans_lt hw)) (K.ex_eq w (hTK.trans_lt hw)) (tr _ _ _ _ (K.u_eq w (hTK.trans_lt hw)) hfr) ?_ θ hθ
      (hSne w hw0)
    obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level (hτ w hw0).1 (hτ w hw0).2 hc₁ hc₂).1
    obtain ⟨z', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu z
    exact ⟨z', hz⟩
  obtain ⟨rfl, rfl⟩ : c₁ = d₁ ∧ c₂ = d₂ := by
    obtain ⟨w, fr, hw, hfr⟩ := hex
    obtain ⟨lam, f, hlam, hf, hf0, -, -, hfS⟩ := key w hw fr hfr
    exact huniq c₁ c₂ hc₁ hc₂ w (hT0.trans_lt hw) (fun v => lam * f v) (hf.const_mul _)
      (fun v => mul_ne_zero hlam (hf0 v)) fun v => by rw [hfS]; ring
  refine ⟨κ, hκ, hdS, fun w _ => ?_, fun U s r hU _ hpull => ?_⟩
  · have e : (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) =
        fun z => (Λ.u.ex (K.h.symm z).2).left := funext fun z => Λ.ex0_b _
    rw [e]
    refine isFnInRigFrame_of_isFn Λ.u Λ.rig hfn (p := fun z => (K.h.symm z).2) K.h.symm.differentiable.snd
      (by simp) (Q := fun z => Q (K.h.symm z)) (hQ.comp K.h.symm.differentiable) (by simp [hQ0]) fun z => ?_
    rw [hoff w, ContinuousLinearEquiv.apply_symm_apply]
    ring
  · obtain ⟨T', hT'⟩ := GlobalTheory.T.arcSection_value_at_specialised_points_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r hfin hth hθ
      hθ0 hfn r₂ r₁ r₀ hU hpull
    refine ⟨max T T', fun w hw => ?_⟩
    have hw1 : T < w.im := (le_max_left _ _).trans_lt hw
    have hw0 := hT0.trans_lt hw1
    obtain ⟨rw, hrw, hval⟩ := hT' w ((le_max_right _ _).trans_lt hw)
    refine ⟨rw, hrw, fun fr hfr z x j k j₀ hx hx' hj hj₀ => ?_⟩
    obtain ⟨v, rfl⟩ := K.h.surjective z
    obtain ⟨lam, f, hlam, hf, hf0, hf1, hfr', hfS⟩ := key w hw1 fr hfr
    obtain ⟨v₀, hv₀⟩ := hSne w hw0
    have hlk : lam = κ := by
      have := eq_at_zero_of_eq_off_zeros (AnArc.differentiable_Sum hT one_ne_zero hθ hw0).continuous
        (hf.const_mul lam) (hQ.cexp.const_mul κ) hv₀ fun v hv => by
          have h1 := hfS v
          have h2 : thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) ≠ 0 := fun h0 => hv (by rw [h1, h0]; simp)
          refine mul_right_cancel₀ h2 ?_
          rw [← hSum w hw0 v, h1]
          ring
      simpa [hf1, hQ0] using this
    have hx2 : x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left := hx.trans (K.ex_eq w (hTK.trans_lt hw1) v)
    have hch : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
      rw [← hx2]
      exact fun p hp => Set.mem_iInter.1 (hj₀ hp).1 PUnit.unit
    rw [hval v x j k j₀ hx2 hx' hj hj₀, hfr' v j₀ hch, hfS, hlk]
    ring

end GlobalTheory.ArcPts
