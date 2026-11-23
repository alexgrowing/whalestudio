import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootMetricFinitelyManyPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDecompositionClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointBelowAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAverageOverLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem HtTieRead.isClosed_basePt {D : D7} (O : Setup D) (y : Pt O.s) : IsClosed ({basePt O.Φ y} : Set (O.var (compPt O.s y)).X) := by
  obtain ⟨p, -, -, e⟩ := liesUnder_basePt O.Φ y
  rw [← e]
  exact GlobalTheory.T.closed_point_below_algebraic _ _ p

theorem HtTieRead.mean_eq {D : D7} {O : Setup D} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    (y : Pt O.s) (f : (T.M (compPt O.s y)).Fun) (g : ∀ σ, Pts (O.var (compPt O.s y)) σ → ℝ)
    (e : ∀ a i, f a (h.pts.conj (compPt O.s y) y a i) = g _ ((h.man _).pt a (h.pts.conj (compPt O.s y) y a i))) :
    h.pts.mean (compPt O.s y) y f =
      (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (w : Pts (O.var (compPt O.s y)) σ) (_ : under w = basePt O.Φ y), g σ w) /
        ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {z : AlgPt (O.var (compPt O.s y)) // below z.1 = basePt O.Φ y} : ℝ)) := by
  rw [← GlobalTheory.T.height_average_over_lifts _ _ _ _ (h.man (compPt O.s y)) _ _ _ g (HtTieRead.isClosed_basePt O y) (h.pts_is.conj y)]
  simp only [Real0.Pts.mean, e]

theorem htTie_of_reads : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
    O.MbIs → HtTie A H h.pts := by
  intro D O A T H h hM
  refine ⟨fun B y g hg => h.pts_is.ar B y g hg, fun y => ⟨fun u u' => ?_, fun a u => ?_⟩, fun y => h.mem_int_iff y,
    fun u y hy => ?_, fun B hB => ⟨fun y => (h.ht.hA y).trans (h.pts_is.a B hB y).symm,
    fun u s hu hs hd hsm y => ?_⟩⟩
  · rw [h.ht.h0 _ y, h.ht.h0 u y, h.ht.h0 u' y]
    simp only [Setup.htWt, ← neg_add, ← Finset.sum_add_distrib, ← add_mul]
    rfl
  · rw [h.ht.h0 _ y, h.ht.h0 u y]
    simp only [Setup.htWt, smul_eq_mul, mul_neg, Finset.mul_sum, ← mul_assoc]
    rfl
  · refine (h.ht.hH u y hy).trans ((GlobalTheory.T.height_weight_root_change D O _ u _ (HtTieRead.isClosed_basePt O y)).trans ?_)
    exact congrArg₂ (· + ·) (h.ht.h0 u y).symm
      (HtTieRead.mean_eq h y _ (O.chg _ none u) fun a i => (h.an _).ph u a _ ((h.mem_int_iff y).1 hy a i)).symm
  · have hu'' : A.sh u s = fun τ i => u τ i - s * O.met.dir τ i := by
      rw [← h.aux.dir]
      rfl
    have hc := hM B hB u s hu hs _ hu'' hd (compPt O.s y)
    have W := h.mdl (FlagAr.setB O.Y B) (compPt O.s y)
    have e₁ := GlobalTheory.T.height_decomposition_closed_point _ _ _ _ _ _ _ _ hc (fun o z => by
      cases o with
      | none => exact GlobalTheory.T.adelic_metric_finitely_many_places _ _ _ _ _ _ _ W.k_pos.ne' W.amp_spec z
      | some x =>
        exact GlobalTheory.T.root_metric_finitely_many_places D O _ _ x z fun st hst =>
          GlobalTheory.T.adelic_metric_finitely_many_places _ _ _ _ _ _ _ one_ne_zero (W.line_spec _ subset_rfl st hst) z) _ (HtTieRead.isClosed_basePt O y)
    have e₂ := HtTieRead.mean_eq h y ((T.F _).phS (A.sh u s) s)
      (fun σ z => O.met.reg _ σ (A.sh u s) (Real.exp (-((s : ℝ) ^ 2)⁻¹)) z / 2) fun a i =>
      (h.an _).phS (A.sh u s) s (by exact_mod_cast hs) a _
    have e₃ := h.pts_is.ar B y _ (hsm (compPt O.s y))
    have e₄ := h.pts_is.L B hB y (A.sh u s)
    have e₅ := h.pts_is.a B hB y
    refine (h.aux.ht (O.Mb B u s) y).trans (e₁.trans ?_)
    rw [map_add, map_add, map_smul, smul_eq_mul]
    erw [e₃, e₄, e₅, e₂]
    simp only [Fintype.sum_option, Option.elim, Setup.htWt, neg_mul, Finset.sum_neg_distrib]
    ring

end GlobalTheory.Mean4O
