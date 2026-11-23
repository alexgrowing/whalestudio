import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordBoundLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

open Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpChartMetric

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ} {g : ℕ}

theorem eq_sum_vec {y : CxPts (genStr Z) σ} (f : EigFrame Z σ (y.1 ≫ genι Z)) (v : TanM (y.1 ≫ genι Z) Z.t.G) :
    v = ∑ p : Pad.Letter Dw, (eigBasis f).repr v p • f.vec p.1 p.2 := by
  conv_lhs => rw [← (eigBasis f).sum_repr v]
  simp only [eigBasis_apply]

theorem dir_eq_sum {y : CxPts (genStr Z) σ} (ε : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left))
    (e0 : ε 0 = (1 : Over.mk (y.1 ≫ genι Z) ⟶ Z.t.G).left)
    (huniq : ∀ v, IsTanAtG Z.t (y.1 ≫ genι Z) v → ∃! w, IsDerivAt0 ε w v) (f : EigFrame Z σ (y.1 ≫ genι Z))
    (W : Pad.Letter Dw → Fin g → ℂ) (hW : ∀ z : Pad.Letter Dw, IsDerivAt0 ε (W z) (f.v z.1 z.2))
    (v : TanM (y.1 ≫ genι Z) Z.t.G) (w : Fin g → ℂ) (hw : IsDerivAt0 ε w (tv v).left) :
    w = ∑ p : Pad.Letter Dw, (eigBasis f).repr v p • W p := by
  classical
  let q := Fintype.equivFin (Pad.Letter Dw)
  have hc : IsCombAtG Z.t (y.1 ≫ genι Z) (fun i => (tv (f.vec (q.symm i).1 (q.symm i).2)).left)
      (fun i => (eigBasis f).repr v (q.symm i)) (tv v).left := by
    rw [LieMet.isComb_iff]
    conv_lhs => rw [eq_sum_vec f v]
    exact (Equiv.sum_comp q.symm (fun p => (eigBasis f).repr v p • f.vec p.1 p.2)).symm
  have h2 := ExpDirs.isDerivAt0_of_comb e0 (fun i => f.tan (q.symm i).1 (q.symm i).2) (fun i => hW (q.symm i))
    (isTan_tv v) hc
  rw [Equiv.sum_comp q.symm (fun p => (eigBasis f).repr v p • W p)] at h2
  exact (huniq _ (isTan_tv v)).unique hw h2

end Point

section Point2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ} {g : ℕ}

theorem met_eq_sum_gram (x : OddPrimesWithRootsOfUnity Z) {y : CxPts (genStr Z) σ} (f : EigFrame Z σ (y.1 ≫ genι Z))
    (v : TanM (y.1 ≫ genι Z) Z.t.G) :
    x.met σ y v v = ∑ τ, star (fun b => (eigBasis f).repr v ⟨τ, b⟩) ⬝ᵥ
      x.gram y f τ *ᵥ (fun b => (eigBasis f).repr v ⟨τ, b⟩) := by
  classical
  set a : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂ := fun τ b => (eigBasis f).repr v ⟨τ, b⟩ with ha
  have hv : v = ∑ τ, ∑ b, a τ b • f.vec τ b := by
    conv_lhs => rw [eq_sum_vec f v]
    exact Fintype.sum_sigma _
  have hoff : ∀ τ τ', τ ≠ τ' → x.met σ y (∑ b, a τ b • f.vec τ b) (∑ b, a τ' b • f.vec τ' b) = 0 := by
    intro τ τ' hne
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, x.met_vec_eq_zero f f hne,
      smul_zero, Finset.sum_const_zero]
  conv_lhs => rw [hv]
  rw [map_sum (x.met σ y), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum (x.met σ y _), Finset.sum_eq_single τ (fun τ' _ h => hoff τ τ' (Ne.symm h)) (by simp)]
  exact form_sum _ _ _ _

theorem sq_norm_dir_le (x : OddPrimesWithRootsOfUnity Z) {y : CxPts (genStr Z) σ} (ε : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left))
    (e0 : ε 0 = (1 : Over.mk (y.1 ≫ genι Z) ⟶ Z.t.G).left)
    (huniq : ∀ v, IsTanAtG Z.t (y.1 ≫ genι Z) v → ∃! w, IsDerivAt0 ε w v) (f : EigFrame Z σ (y.1 ≫ genι Z))
    (W : Pad.Letter Dw → Fin g → ℂ) (hW : ∀ z : Pad.Letter Dw, IsDerivAt0 ε (W z) (f.v z.1 z.2)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → ℂ), ‖∑ b, u b • W ⟨τ, b⟩‖ ^ 2 ≤ C * (star u ⬝ᵥ x.gram y f τ *ᵥ u).re)
    (v : TanM (y.1 ≫ genι Z) Z.t.G) (w : Fin g → ℂ) (hw : IsDerivAt0 ε w (tv v).left) :
    ‖w‖ ^ 2 ≤ (Fintype.card (E →+* ℂ) : ℝ) * C * (x.met σ y v v).re := by
  classical
  set a : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂ := fun τ b => (eigBasis f).repr v ⟨τ, b⟩ with ha
  have hw' : w = ∑ τ, ∑ b, a τ b • W ⟨τ, b⟩ := by
    rw [dir_eq_sum ε e0 huniq f W hW v w hw]
    exact Fintype.sum_sigma _
  have h1 : ‖w‖ ≤ ∑ τ, ‖∑ b, a τ b • W ⟨τ, b⟩‖ := hw' ▸ norm_sum_le _ _
  have h2 : ‖w‖ ^ 2 ≤ (Fintype.card (E →+* ℂ) : ℝ) * ∑ τ, ‖∑ b, a τ b • W ⟨τ, b⟩‖ ^ 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun τ : E →+* ℂ => ‖∑ b, a τ b • W ⟨τ, b⟩‖)
    simpa [Finset.card_univ] using this
  refine h2.trans ?_
  rw [met_eq_sum_gram x f v, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [_root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC τ (a τ)) (Nat.cast_nonneg _)

end Point2

set_option maxHeartbeats 1000000 in

theorem exp_coord_sq_le_met : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g), IsExpChart e ex → ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (v : TanM (y.1 ≫ genι s.T.Z) s.T.Z.t.G) (w : Fin g → ℂ), IsDerivAt0 (fun u => (ex y u).left) w (tv v).left → ‖w‖ ^ 2 ≤ C * (x.met σ y v v).re := by
  intro D A N j S κ s x σ n g e ex he y₀ hy₀
  classical
  obtain ⟨U, hU, C, hC0, hC⟩ := h0_le_exp_coord D A N j S κ s x σ n g e ex he y₀ hy₀
  obtain ⟨V, φ, F, B, a, hB, hb₀, hBt, ha, hab⟩ :=
    exists_frameFam_of_isExpChart _ _ _ _ _ _ _ _ _ σ n g e ex he y₀ hy₀
  refine ⟨U ∩ (e.source ∩ e ⁻¹' B), Filter.inter_mem hU (Filter.inter_mem (e.open_source.mem_nhds hy₀)
    ((e.continuousAt hy₀).preimage_mem_nhds (hB.mem_nhds hb₀))), (Fintype.card (D.host.E →+* ℂ) : ℝ) * C,
    by positivity, ?_⟩
  rintro y ⟨hyU, hy, hyB⟩ v w hw
  have hab1 : (a (e y)).1 = y := (hab _ hyB).1.trans (e.left_inv hy)
  obtain ⟨p, hp⟩ : ∃ p : CxFr s.T.Z σ, p.1 = y := ⟨a (e y), hab1⟩
  obtain ⟨y₁, f⟩ := p
  dsimp only at hp
  subst hp
  have e0 : ex y₁ 0 = 1 := by simpa using he.2.2.2.1 _ hy 0 0
  have huniq := (he.2.2.2.2.2 y₁ hy).2
  choose W hW using fun z : Pad.Letter S.Dw => (huniq _ (f.tan z.1 z.2)).exists
  exact sq_norm_dir_le x (fun u => (ex y₁ u).left) (congrArg (·.left) e0) huniq f W hW hC0
    (fun τ u => (hC y₁ hyU f W hW τ u).1) v w hw

end GlobalTheory.ExpChartMetric
