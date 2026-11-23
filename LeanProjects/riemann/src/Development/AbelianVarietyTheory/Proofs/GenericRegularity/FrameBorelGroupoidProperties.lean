import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.Reg.BorelGroupoid

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lower_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (lt_of_le_of_lt (not_lt.mp hk) hij), mul_zero]

theorem lower_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lower_of_mul_eq_one (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : B * A = 1) : ∀ i j, i < j → B i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  have hd : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hB
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  rw [Matrix.inv_eq_left_inv hB] at h'
  exact fun i j hij => h' hij

end Tri

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem chg_refl (y : FrPt Xo c S) : FrChg (fun _ => 1) 1 y y := by
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := Formalism.L2.PjFree.isCombAt_single (y.tan τ) i
    have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i = Pi.single i 1 := by
      funext j
      rw [Matrix.one_apply, Pi.single_apply]
      simp only [eq_comm]
    rw [← e] at h
    exact h
  · rw [Model.scal_one, _root_.one_mul]

theorem chg_comp {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S}
    {y y' y'' : FrPt Xo c S} (h : FrChg g a y y') (h' : FrChg g' a' y' y'') :
    FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  obtain ⟨hx, hc, hs⟩ := h
  obtain ⟨hx', hc', hs'⟩ := h'
  obtain ⟨x', xo', u', t', e', b', s', gen'⟩ := y'
  obtain ⟨x'', xo'', u'', t'', e'', b'', s'', gen''⟩ := y''
  dsimp only at hx hx' hc hc' hs hs'
  subst hx'
  subst hx
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u' τ) (g τ).transpose
      (g' τ i) (u'' τ i) (fun k => hc τ k) (hc' τ i)
    have e : (g τ).transpose.mulVec (g' τ i) = (g' τ * g τ) i := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => _root_.mul_comm _ _
    rw [e] at h
    exact h
  · have e1 := (Model.secBC_id_iff _ _ _ _).1 hs i
    have e2 := (Model.secBC_id_iff _ _ _ _).1 hs' i
    dsimp only
    rw [e2, e1, Model.scal_mul, _root_.mul_assoc]

end Geo

theorem frBor_groupoid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨fun y => ?_, fun t t' y y' y'' h h' => ?_, fun t y y' h => ?_, fun t t' y y' h h' => ?_⟩
  · refine (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_, fun τ i j hij => ?_, chg_refl y⟩
    · exact Matrix.one_apply_eq i
    · exact Matrix.one_apply_ne hij.ne
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', hz', hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    refine (Model.frBor_iff _ _ _).2 ⟨fun τ => g' τ * g τ, fun τ i => ?_,
      fun τ => lower_mul _ _ (hz' τ) (hz τ), ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lower_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul, _root_.mul_comm]
    · rw [Pi.mul_apply, Units.val_mul, _root_.mul_comm]
      exact chg_comp hc hc'
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', a', hc'⟩ := Model.exists_frChg y' y hc.1.symm
    obtain ⟨e1, e2⟩ := Model.frChg_unique (chg_comp hc hc') (chg_refl y)
    have hinv : ∀ τ, g' τ * g τ = 1 := fun τ => congrFun e1 τ
    have hz' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ => lower_of_mul_eq_one _ _ (hz τ) (hinv τ)
    refine (Model.frBor_iff _ _ _).2 ⟨g', fun τ i => ?_, hz', ?_⟩
    · have h2 := lower_mul_diag _ _ (hz' τ) (hz τ) i
      rw [hinv, Matrix.one_apply_eq, hd] at h2
      rw [Pi.inv_apply]
      exact Units.eq_inv_of_mul_eq_one_right h2.symm
    · have : a' = ((t⁻¹ none : Sˣ) : S) := by
        rw [Pi.inv_apply]
        exact Units.eq_inv_of_mul_eq_one_right e2
      exact this ▸ hc'
  · obtain ⟨g, hd, -, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', -, hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    obtain ⟨e1, e2⟩ := Model.frChg_unique hc hc'
    funext k
    apply Units.ext
    rcases k with _ | ⟨τ, i⟩
    · exact e2
    · rw [← hd, ← hd', e1]

end GlobalTheory.Reg.BorelGroupoid
