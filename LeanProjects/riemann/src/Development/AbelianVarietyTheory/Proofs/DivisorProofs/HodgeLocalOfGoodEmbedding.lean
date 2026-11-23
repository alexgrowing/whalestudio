import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibreStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurvInterp.HodgeGood

open Formalism.L2.Pj GlobalTheory.LieBase GlobalTheory.ShFam.Hor.ExpDirs ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := by
  rw [unfFam, dif_pos rfl]

theorem isHodgeFrame_of_eq {V V' : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hV : V σ = V' σ) {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)} (h : IsHodgeFrame V y f) :
    IsHodgeFrame V' y f := by
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := h
  rcases h1 with rfl | rfl
  · obtain rfl : σ' = σ := h2.trans (RingHom.id_comp σ)
    have key : ∀ (W : Formalism.L2.PjFree.Unf Xo c σ' r), W = V' σ' → ∀ (k : W.Comp) (x : (W.X k).dom),
        IsOrth (W.X k) x.1 → (cxPt Z (W.un k x)).1 = spMap (RingHom.id ℂ) ≫ y.1 →
        f.IsMap (RingHom.id ℂ) (cxFrame Z (W.un k x)) → IsHodgeFrame V' y f := by
      rintro W rfl k x a b d
      exact ⟨RingHom.id ℂ, σ', k, x, .inl rfl, (RingHom.id_comp σ').symm, hσ, a, b, d⟩
    exact key (V σ') hV k x h4 h5 h6
  · exact (not_good_conj c (σ := σ) hσ (h2 ▸ h3)).elim

end Free

theorem hodge_gram_eq_hodgeMet {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {σ : κ.c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) {y : CxPts (genStr s.T.Z) σ} (hy : Inner y)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram y g τ = ((xiR D : ℝ) : ℂ) • (hodgeMet s.T.Z (s.U σ)).gram y g τ := by
  have hU : ∀ σ', Formalism.L2.PjFree.GoodEmb κ.c σ' → Formalism.L2.PjFree.IsUnf (s.U σ') := fun σ' h => (s.unf σ' h).1
  obtain ⟨f, hf⟩ := exists_isHodgeFrame hU (y := y) hy
  have h : ∃ f, IsHodgeFrame (unfFam (s.U σ)) y f := ⟨f, isHodgeFrame_of_eq hσ (unfFam_self _).symm hf⟩
  have hc : IsHodgeFrame s.U y h.choose := isHodgeFrame_of_eq hσ (unfFam_self _) h.choose_spec
  rw [x.hodge_gram hc g τ]
  show _ = _ • (EigMet.hodge (unfFam (s.U σ)) (2 * Real.pi) Real.two_pi_pos _).gram y g τ
  rw [show (EigMet.hodge (unfFam (s.U σ)) (2 * Real.pi) Real.two_pi_pos
    (Classical.arbitrary (EigMet s.T.Z σ))).gram y g τ = _ from dif_pos h, smul_smul]
  congr 1
  push_cast
  ring

theorem chart_of_rank {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) {r : ℕ} (hr : Dw.p + Dw.q = r)
    (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (x₀ : GlobalTheory.CxPts (genStr T.Z) σ) :
    ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
      (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ))
      (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧
      x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧
      (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧
      ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z))
        (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W →
        (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' =>
          hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧
        ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 →
          hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  subst hr
  exact GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre E H Dw l Xo c O β Y T σ U hσ hU x₀

theorem mul_conjTranspose_apply {m m' : Type} [Fintype m] [Fintype m'] {g : ℕ} (Q : Matrix m (Fin g) ℂ)
    (M : Matrix (Fin g) (Fin g) ℂ) (Q' : Matrix m' (Fin g) ℂ) (b : m) (b' : m') :
    (Q * M * Q'ᴴ) b b' = hermForm M (Q b) (Q' b') := by
  simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.CurvInterp.HodgeGood

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurvInterp.HodgeGood

open Formalism.L2.Pj GlobalTheory.LieBase GlobalTheory.ShFam.Hor.ExpDirs

theorem hodgeLocal_good : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → HodgeLocal x σ := by
  intro D A N j S κ s x σ hσ e B a hB h0 ha hc
  obtain ⟨n, k, hk, g, rk, τ₀, Bm, ch₀, ex, κc, hP, hex, hx0, hch0, hcard, hκ, hInner, hmain⟩ :=
    chart_of_rank A.H S.Dw κ.l (S.Xo κ.l) κ.c (𝓞 κ.c.F) (algebraMap (𝓞 κ.c.F) κ.c.F) s.Ygl s.T σ S.rank_eq (s.U σ) hσ
      (s.unf σ hσ).1 (a 0).1
  set B' : Set (Fin e → ℂ) := B ∩ (fun z => (a z).1) ⁻¹' ch₀.source with hB'
  have hB'o : IsOpen B' := hc.isOpen_inter_preimage hB ch₀.open_source
  have h0' : (0 : Fin e → ℂ) ∈ B' := ⟨h0, hx0⟩
  have hB'B : B' ⊆ B := Set.inter_subset_left
  have src : ∀ z ∈ B', (a z).1 ∈ ch₀.source := fun z hz => hz.2
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 hB'o 0 h0'
  have hhol' : IsHolTo B' (fun z => (a z).1.1) := GlobalTheory.LocLift.isHolTo_mono ha.1 hB'o hB'B
  have htan : ∀ τ i, HolTan B' fun z => (a z).2.v τ i := fun τ i U f =>
    (ha.2 τ i U f).mono fun z hz => ⟨hB'B hz.1, hz.2⟩
  have h5 := fun z (hz : z ∈ B') => hex.2.2.2.2.2 _ (src z hz)
  choose! Wa hWa using fun z (hz : z ∈ B') (q : Σ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ)) => ((h5 z hz).2 _ ((a z).2.tan q.1 q.2)).exists
  have hWd : ∀ z ∈ B', ∀ q, DifferentiableAt ℂ (fun z => Wa z q) z := fun z hz q =>
    differentiableAt_dir hex hB'o hhol' src (htan q.1 q.2) (fun b hb => hWa b hb q) hz
  refine ⟨ρ, hρ, hρB.trans hB'B, ?_⟩
  unfold IsBlockModel
  refine ⟨n, k, hk, g, rk, τ₀, Bm, fun z => ch₀ (a z).1, fun τ z => Matrix.of fun i l => Wa z ⟨τ, i⟩ l,
    fun τ => xiR D * κc τ, hP, ?_, hch0, ?_, ?_, hcard, ?_, fun τ => mul_pos (GlobalTheory.ShFam.xiR_pos D) (hκ τ), ?_⟩
  · refine differentiableOn_pi.2 fun m => ?_
    exact hex.2.1 m (Fin e → ℂ) (Metric.ball 0 ρ) (fun z => (a z).1) Metric.isOpen_ball
      (GlobalTheory.LocLift.isHolTo_mono hhol' Metric.isOpen_ball hρB) fun z hz => src z (hρB hz)
  · intro z hz m
    have h := ch₀.map_source (src z (hρB hz))
    rw [hex.1, mem_ball_zero_iff] at h
    exact (norm_le_pi_norm _ m).trans_lt h
  · intro τ i l z hz
    exact (differentiableAt_pi.1 (hWd z (hρB hz) ⟨τ, i⟩) l).differentiableWithinAt
  · have e0 : ex (a 0).1 0 = 1 := by simpa using hex.2.2.2.1 _ hx0 0 0
    obtain ⟨bs, hbs⟩ := dirs_basis (a 0).2 (e := fun w => (ex (a 0).1 w).left) (congrArg (·.left) e0)
      (h5 0 h0').1 (h5 0 h0').2 (fun q => hWa 0 h0' q)
    have : (fun p : Σ τ, Fin (S.Dw.mult τ) => (Matrix.of fun i l => Wa 0 ⟨p.1, i⟩ l) p.2) = Wa 0 := by
      funext p; rfl
    simp only [] at this ⊢
    rw [this, ← hbs]
    exact bs.linearIndependent
  · intro z hz hin
    have hs := src z (hρB hz)
    have hD : Dirs ⟨(a z).1, (a z).2⟩ (fun w => (ex (a z).1 w).left) (Wa z) := fun q => hWa z (hρB hz) q
    obtain ⟨hm1, hm2⟩ := hmain _ hs hin (a z).2 (Wa z) hD
    refine ⟨⟨?_, (hInner _ hs).1 hin⟩, fun τ => ?_, fun τ τ' hne => ?_⟩
    · intro m
      have h := ch₀.map_source hs
      rw [hex.1, mem_ball_zero_iff] at h
      exact (norm_le_pi_norm _ m).trans_lt h
    · ext b b'
      dsimp only
      rw [Matrix.transpose_apply, hodge_gram_eq_hodgeMet x hσ hin, hm1, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.smul_apply, mul_conjTranspose_apply, Matrix.of_apply, smul_smul]
      congr 1
      push_cast
      ring
    · ext b b'
      dsimp only
      rw [mul_conjTranspose_apply, Matrix.zero_apply]
      exact hm2 ⟨τ, b⟩ ⟨τ', b'⟩ hne

end GlobalTheory.CurvInterp.HodgeGood
