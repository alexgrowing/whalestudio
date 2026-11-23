import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.BcPull

theorem isom_of_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (L M : MLine p σ)
    (e : M.B.ι → L.B.ι) (hU : ∀ a, M.B.U a ≤ L.B.U (e a))
    (hg : ∀ (x : X) a a', x ∈ M.B.U a → x ∈ M.B.U a' →
      gm (𝟙 X) x (M.B.U a ⊓ M.B.U a') (M.B.g a a') = gm (𝟙 X) x (L.B.U (e a) ⊓ L.B.U (e a')) (L.B.g (e a) (e a')))
    (hφ : ∀ a, ∀ y ∈ ptsIn p σ (M.B.U a), M.φ.φ a y = L.φ.φ (e a) y) : L.Isom M := by
  have le (c : M.B.ι × L.B.ι) : M.B.U c.1 ⊓ L.B.U c.2 ≤ L.B.U (e c.1) ⊓ L.B.U c.2 := inf_le_inf_right _ (hU c.1)
  refine ⟨⟨fun c => res (le c) (L.B.g (e c.1) c.2)⟩, fun c c' => Geo.Tor.unit_ext fun x hx => ?_, fun a b y ha hb => ?_⟩
  · have hx' : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ (M.B.U c'.1 ⊓ L.B.U c'.2) := hx
    refine ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c) hx'.1 _)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (Geo.Tor.gm_div L.B M.B (𝟙 X) x c c' hx')
      ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c') hx'.2 _))).trans ?_)
    have h₁ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) (hU _ hx'.2.1) hx'.2.2
    have h₂ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) hx'.1.2 hx'.2.2
    rw [hg x _ _ hx'.1.1 hx'.2.1, mul_right_comm, h₁, ← h₂, mul_inv_cancel_right]
  · rw [hφ a y ha, L.φ.trans (e a) b y (ptsIn_mono (hU a) ha) hb, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact congrArg (fun z : ℂ => _ + Real.log (‖z‖ ^ 2))
      (CxPts.ev_res (le (a, b)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) _).symm

theorem bc_φ {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    {ρ : k →+* K} (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) (i : PUnit → A.B.ι) (z : CxPts q τ) :
    (A.bc w τ).φ.φ i z = A.φ.φ (i PUnit.unit) (bcPt w τ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * A.φ.φ (i a) (bcPt w τ z)).trans (by simp)

theorem bc_pull_isom : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G Z G' : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (w : j ≫ p = q ≫ spMap ρ) (i : Z ⟶ X) (j' : G' ⟶ Z) (g : G' ⟶ G), g ≫ j = j' ≫ i → ∀ (w' : j' ≫ i ≫ p = (g ≫ q) ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)), ((A.pull i rfl).bc w' τ).Isom ((A.bc w τ).pull g rfl) := by
  intro k K _ _ ρ X G Z G' p q j w i j' g h w' τ A
  have hm (a : PUnit → PUnit → A.B.ι) (x : G') (hx : x ∈ ((A.B.pull j).pull g).U a) :
      x ∈ ((A.B.pull i).pull j').U a := by
    have h₀ : j (g x) ∈ A.B.U (a PUnit.unit PUnit.unit) := Geo.Tor.mem_pull.1 (Geo.Tor.mem_pull.1 hx)
    have h₁ : (g ≫ j) x ∈ A.B.U (a PUnit.unit PUnit.unit) := h₀
    rw [h] at h₁
    exact Geo.Tor.mem_pull.2 (Geo.Tor.mem_pull.2 h₁)
  refine isom_of_chart _ _ (fun a : PUnit → PUnit → A.B.ι => a) hm
    (fun x (a a' : PUnit → PUnit → A.B.ι) ha ha' => ?_) fun (a : PUnit → PUnit → A.B.ι) y _ => ?_
  · refine ((Geo.Tor.gm_pull_g (A.B.pull j) g (𝟙 G') x a a' ha ha').trans
      (Geo.Tor.gm_pull_g A.B j (𝟙 G' ≫ g) x _ _ (Geo.Tor.mem_pull.1 ha) (Geo.Tor.mem_pull.1 ha'))).trans (Eq.symm ?_)
    refine ((Geo.Tor.gm_pull_g (A.B.pull i) j' (𝟙 G') x a a' (hm a x ha) (hm a' x ha')).trans
      (Geo.Tor.gm_pull_g A.B i (𝟙 G' ≫ j') x _ _ (Geo.Tor.mem_pull.1 (hm a x ha))
        (Geo.Tor.mem_pull.1 (hm a' x ha')))).trans ?_
    rw [Category.assoc, Category.assoc, h]
  · refine (((A.bc w τ).φ.pull_φ g rfl a y).trans (bc_φ w τ A _ _)).trans (Eq.symm ?_)
    refine ((bc_φ w' τ (A.pull i rfl) a y).trans (A.φ.pull_φ i rfl _ _)).trans (congrArg _ (Subtype.ext ?_))
    change (y.1 ≫ j') ≫ i = (y.1 ≫ g) ≫ j
    rw [Category.assoc, Category.assoc, h]

end GlobalTheory.Mix.BcPull
