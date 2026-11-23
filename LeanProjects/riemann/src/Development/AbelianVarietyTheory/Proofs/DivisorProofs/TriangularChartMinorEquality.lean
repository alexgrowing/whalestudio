import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColMinorEqSupMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMatricesValueMultiplicative
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame

theorem colMinor_eq_of_max {K : Type} [Field K] (w : AbsoluteValue K ℝ) {n g : ℕ} (M : Matrix (Fin n) (Fin g) K)
    (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) (h : ∀ τ, w (minorAt M k hk τ) ≤ w (minorAt M k hk σ))
    (S : Finset (Fin g)) (hS : ∀ l, l ∈ S ↔ (l : ℕ) < k) : colMinor w M S = w (minorAt M k hk σ) := by
  have e : S = Finset.univ.filter fun l : Fin g => (l : ℕ) < k := by
    ext l
    simp [hS]
  rw [e, colMinor_filter_lt_eq_iSup_minorAt w M k hk]
  exact le_antisymm (Real.iSup_le h (w.nonneg _))
    (le_ciSup (f := fun τ => w (minorAt M k hk τ)) (Set.finite_range _).bddAbove σ)

theorem lg_eq_log_frameC : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ} {C : CxSt F} (A : Fin g → Adl C Y) (U' : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ChartReg V U' H T → (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) → (∀ i y, UnitAt y (genAt (A i).D y * d y i)) → MinorNorm V W U' H d T A p → AtTest V W p fun v e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ i, (A i).lg v e y = Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (frameC H σ i : V.G.functionField)))) := by
  intro F _ _ Y V W p _ _ g C A U' H d T σ hT hreg _ hunit hmax hgen hnorm v hv e y hy z yt hz hyt hU i
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hin : V.j (below z) ∈ U' := by
    have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      change (z ≫ V.j) _ = _
      rw [← hyt]; rfl
    rw [e2]; exact hU trivial
  have hu := hunit (below z) hin
  have hr := hreg (below z) hin
  rw [hπ] at hu hr
  have hm := hmax v hv e y hy z yt hz hyt hU
  have hl := (hnorm v hv e y hy z yt hz hyt hU).2 i
  obtain ⟨hTt, hTd⟩ := hT (below y.1)
  have htri : ((T (below y.1)).map V.φ).BlockTriangular id := fun a b hab => by
    rw [Matrix.map_apply, hTt hab, map_zero]
  have hdiag : ∀ j, (T (below y.1)).map V.φ j j = V.φ (d (below y.1) j : Y.Fn) := fun j => by
    rw [Matrix.map_apply, hTd]
  have hne : ∀ k hk, minorAt (H * ((T (below y.1)).map V.φ)⁻¹) k hk (σ k) ≠ 0 := fun k hk h0 => by
    have h1 := SmallSec.valAt_ne_zero (hu k hk)
    rw [h0, Res.valAt_zero] at h1
    exact h1 rfl
  have hc := (triChange H _ htri (fun j => by rw [hdiag]; exact (map_ne_zero _).2 (Units.ne_zero _)) σ).2.2 hne i
  have hgu : UnitAt (V.π (below z)) (genAt (A i).D (below y.1) * d (below y.1) i) := by rw [hπ]; exact hgen i _
  obtain ⟨-, hmin, hdiv⟩ := CramerValues.values_regular z
  have hval : ∀ k hk, valAt z (minorAt (H * ((T (below y.1)).map V.φ)⁻¹) k hk (σ k)) =
      minorAt (valMat V H (T (below y.1)) z) k hk (σ k) := fun k hk => (hmin _ hr k hk (σ k)).2
  have hw : ∀ k hk, e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k)) ≠ 0 := fun k hk => by
    rw [← hval]
    exact (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hu k hk))
  have hg0 : e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i)) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hgen i _))
  rw [hl, colMinor_eq_of_max e.w _ ((i : ℕ) + 1) i.2 _ (hm _ _) _ (fun l => Finset.mem_Iic.trans Nat.lt_succ_iff.symm),
    colMinor_eq_of_max e.w _ (i : ℕ) i.2.le _ (hm _ _) _ (fun l => Finset.mem_Iio),
    hc, hdiag, ← mul_div_assoc, ← mul_assoc, ← map_mul,
    (hdiv _ _ ((V.unitAt_φ hgu).mul (hu _ _)).regAt (hu _ _)).2,
    SmallSec.valAt_mul (V.unitAt_φ hgu).regAt (hu _ _).regAt, V.valAt_φ z hgu.regAt, hz, hval, hval, map_div₀, map_mul,
    Real.log_div (mul_ne_zero hg0 (hw _ _)) (hw _ _), Real.log_mul hg0 (hw _ _)]

end GlobalTheory.ConstLat.CramerFrame

end
