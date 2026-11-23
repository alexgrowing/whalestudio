import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerRegularizedPotentialBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFormIsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffBoundaryComplementVolumeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFormPlurisubharmonicPotentialStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConstServe

section Mono

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem deriv_nonneg_of_monotoneOn {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (hf : MonotoneOn f s) (hs : s ∈ nhds x) :
    0 ≤ deriv f x := by
  rw [← derivWithin_of_mem_nhds hs]
  exact hf.derivWithin_nonneg

theorem isRegConst_mono {a θ : ChartForm p σ d} {Ψ : CxPts p σ → ℝ → ℝ} {A K δ A' K' δ' : ℝ}
    (ha : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, 0 ≤ a c y ξ) (h : IsRegConst a θ Ψ A K δ) (hA : A ≤ A')
    (hK : K ≤ K') (hδ : 0 < δ') (hδ' : δ' ≤ δ) : IsRegConst a θ Ψ A' K' δ' where
  A_nonneg := h.A_nonneg.trans hA
  K_nonneg := h.K_nonneg.trans hK
  δ_pos := hδ
  smooth c := (h.smooth c).mono (prod_mono subset_rfl fun w hw => ⟨hw.1, hw.2.trans_le hδ'⟩)
  mono y s hs t ht hst := by
    have h1 := h.mono y ⟨hs.1, hs.2.trans_le hδ'⟩ ⟨ht.1, ht.2.trans_le hδ'⟩ hst
    have h2 : (K' - K) * s ^ 2 ≤ (K' - K) * t ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hst 2) (sub_nonneg.2 hK)
    simp only at h1 ⊢
    nlinarith
  hess c y hy w hw hwδ ξ η := by
    have h1 := h.hess c y hy w hw (hwδ.trans_le hδ') ξ η
    set f : ℝ → ℝ := fun t => Ψ y t + K * t ^ 2 with hfdef
    have hf0 : 0 ≤ deriv f ‖w‖ :=
      deriv_nonneg_of_monotoneOn (h.mono y) (Ioo_mem_nhds hw (hwδ.trans_le hδ'))
    have hg : deriv (fun t => Ψ y t + K' * t ^ 2) ‖w‖ ≥ deriv f ‖w‖ := by
      have e : (fun t => Ψ y t + K' * t ^ 2) = fun t => f t + (K' - K) * t ^ 2 := by
        funext t; simp only [hfdef]; ring
      rw [e]
      by_cases hd : DifferentiableAt ℝ f ‖w‖
      · have hq : HasDerivAt (fun t : ℝ => (K' - K) * t ^ 2) ((K' - K) * (2 * ‖w‖)) ‖w‖ := by
          simpa using (hasDerivAt_pow 2 ‖w‖).const_mul (K' - K)
        have e2 := (hd.hasDerivAt.add hq).deriv
        rw [show (f + fun t : ℝ => (K' - K) * t ^ 2) = fun t => f t + (K' - K) * t ^ 2 from rfl] at e2
        rw [e2]
        have : 0 ≤ (K' - K) * (2 * ‖w‖) := mul_nonneg (sub_nonneg.2 hK) (by positivity)
        linarith
      · have hd' : ¬ DifferentiableAt ℝ (fun t => f t + (K' - K) * t ^ 2) ‖w‖ := fun h' => hd (by
          have := h'.sub ((differentiableAt_id.pow 2).const_mul (K' - K))
          refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
          simp)
        rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd']
    have ha0 := ha c y hy ξ.ofLp
    have hX : 0 ≤ ‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2 := by positivity
    have hA0 := h.A_nonneg
    have e1 : A * (‖w‖ * deriv f ‖w‖) * a c y ξ.ofLp ≤
        A' * (‖w‖ * deriv (fun t => Ψ y t + K' * t ^ 2) ‖w‖) * a c y ξ.ofLp := by
      apply mul_le_mul_of_nonneg_right _ ha0
      apply mul_le_mul hA _ (mul_nonneg (norm_nonneg _) hf0) (hA0.trans hA)
      exact mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    have e2 : K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
        K' * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) := mul_le_mul_of_nonneg_right hK hX
    linarith

end Mono

section Combine

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag}

theorem exists_commonConst (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ)
    (om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim) (E : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim)
    (hk : ∀ k σ, IsKaehlerForm (AnRead.all (Φ.C k).Y.str σ (Φ.C k).Y.dim) (om k σ))
    (h : ∀ k σ τ (i : Fin N), (i : ℕ) + 1 < N → ∃ a K δ : ℝ,
      IsRegConst (om k σ) (thW h0 k σ (fund τ i)) (rho (om k σ) (E k σ) (phW hm h0 k σ (fund τ i))) a K δ) :
    ∃ a K δ : ℝ, CommonConst hm h0 om E a K δ := by
  classical
  have h' : ∀ q : s.Comp × (D.what₂.LL →+* ℂ) × D.what₂.Tau × Fin N, ∃ a K δ : ℝ, 0 ≤ a ∧ 0 ≤ K ∧ 0 < δ ∧
      ((q.2.2.2 : ℕ) + 1 < N → IsRegConst (om q.1 q.2.1) (thW h0 q.1 q.2.1 (fund q.2.2.1 q.2.2.2))
        (rho (om q.1 q.2.1) (E q.1 q.2.1) (phW hm h0 q.1 q.2.1 (fund q.2.2.1 q.2.2.2))) a K δ) := by
    intro q
    by_cases hq : (q.2.2.2 : ℕ) + 1 < N
    · obtain ⟨a, K, δ, hr⟩ := h q.1 q.2.1 q.2.2.1 q.2.2.2 hq
      exact ⟨a, K, δ, hr.A_nonneg, hr.K_nonneg, hr.δ_pos, fun _ => hr⟩
    · exact ⟨0, 0, 1, le_rfl, le_rfl, one_pos, fun h => absurd h hq⟩
  choose a K δ ha hK hδ hr using h'
  have hS0 : 0 ≤ ∑ q, (δ q)⁻¹ := Finset.sum_nonneg fun q _ => (inv_pos.2 (hδ q)).le
  refine ⟨∑ q, a q, ∑ q, K q, (1 + ∑ q, (δ q)⁻¹)⁻¹, Finset.sum_nonneg fun q _ => ha q,
    Finset.sum_nonneg fun q _ => hK q, by positivity, fun k σ τ i hi => ?_⟩
  have hS : (δ (k, σ, τ, i))⁻¹ ≤ 1 + ∑ q, (δ q)⁻¹ := by
    have := Finset.single_le_sum (f := fun q => (δ q)⁻¹) (fun q _ => (inv_pos.2 (hδ q)).le)
      (Finset.mem_univ (k, σ, τ, i))
    linarith
  refine isRegConst_mono (fun c y hy ξ => ?_) (hr (k, σ, τ, i) hi)
    (Finset.single_le_sum (f := a) (fun q _ => ha q) (Finset.mem_univ _))
    (Finset.single_le_sum (f := K) (fun q _ => hK q) (Finset.mem_univ _)) (by positivity)
    (inv_le_of_inv_le₀ (hδ _) hS)
  by_cases hξ : ξ = 0
  · subst hξ
    have e := (continuous_and_smul (hk k σ) hy).2 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at e
    exact e.ge
  · exact ((hk k σ).2 c y hy ξ hξ).le

end Combine

theorem constSt (hP2 : Hypotheses2) (hPH : HypothesesH) (hD : GlobalTheory.Published.DemaillyRegularisation) (hK : KernelSt) : ConstSt := by
  intro D O x P hc hf hr
  refine P.const (exists_commonConst _ _ _ _ (fun k σ => P.om_kaehler k σ) fun k σ τ i hi => ?_)
  obtain ⟨v, hv, hvψ⟩ := GlobalTheory.T.theta_form_plurisubharmonic_potential hP2 hPH D O x P hc hf hr k σ τ i hi
  obtain ⟨A, K, δ, hreg, -⟩ := hD _ _ _ σ _ inferInstance inferInstance (P.om k σ) (thW (refMet x O.Φ) k σ (fund τ i))
    (P.exph k σ) v (P.om_kaehler k σ) (P.exph_is k σ) (GlobalTheory.T.theta_form_is_closed D O x P hc hf hr k σ _) hv
  obtain ⟨δ', h'⟩ := GlobalTheory.T.kaehler_regularized_potential_bound hK _ _ _ σ _ inferInstance (P.om k σ) _ (P.exph k σ)
    (phW (metsOf x O.Φ) (refMet x O.Φ) k σ (fund τ i)) (fun y => (v y).toReal) (offBd O.Φ k σ)ᶜ
    (P.om_kaehler k σ) (P.exph_is k σ) (fun y hy => (hvψ y (not_not.1 hy)).symm) (GlobalTheory.T.off_boundary_complement_volume_zero D O x P hc hf hr k σ) A K δ hreg
  exact ⟨A, K, δ', h'⟩

end GlobalTheory.ConstServe
