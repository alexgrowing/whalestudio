import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.GradedDiv

section Diag

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {g h : Mat m K}

theorem diag_mul (hg : Par m O g) (hh : Par m O' h) (τ : ι) (i : Fin (m τ)) :
    (g * h) τ i i = g τ i i * h τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h' | h'
  · rw [(hh τ).2.2.2 l i l.2 h', mul_zero]
  · rw [(hg τ).2.2.2 i l i.2 h', zero_mul]

theorem diag_ne_zero (hg : Par m O g) (τ : ι) (i : Fin (m τ)) : g τ i i ≠ 0 := by
  have := diag_mul hg hg.inv τ i
  rw [Mat.mul_inv hg.det_ne] at this
  exact left_ne_zero_of_mul_eq_one (this.symm.trans (Matrix.one_apply_eq i))

end Diag

theorem exists_div {F : Type} [Field F] {Y : GlobalTheory.ProjVar.Var F} {ι : Type} {m : ι → ℕ} (S : Fr (ratOf Y) m m)
    {A₀ : Mat m Y.Fn} (h₀ : A₀ ∈ S.S (genericPoint Y.X)) :
    ∃ gr : ∀ τ, Fin (m τ) → Y.Dv, ∀ y : Y.X, ∃ A ∈ S.S y, ∃ t : ∀ τ, Fin (m τ) → Y.Fnˣ,
      (∀ τ i, (A₀ * A⁻¹) τ i i = t τ i) ∧ (∀ τ i k, i < k → (A₀ * A⁻¹) τ i k = 0) ∧
        ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  have hP : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y →
      Par m ((ratOf Y).O (genericPoint Y.X)).toSubring (A₀ * A⁻¹) := fun hA =>
    (Fr.mem_iff (Fr.mem_genericPoint hA)).1 h₀
  let t : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y → ∀ τ, Fin (m τ) → Y.Fnˣ := fun hA τ i =>
    Units.mk0 _ (diag_ne_zero (hP hA) τ i)
  have hreg : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      RegAt y ((t hA' τ i : Y.Fn) / t hA τ i) := fun {y A A'} hA hA' τ i => by
    have hg := (Fr.mem_iff hA').1 hA
    have e := diag_mul (hP hA) hg τ i
    rw [← mul_assoc, mul_assoc A₀, Mat.inv_mul (Fr.det_ne hA), mul_one] at e
    have e' : (t hA' τ i : Y.Fn) / t hA τ i = (A * A'⁻¹) τ i i := by
      rw [div_eq_iff (t hA τ i).ne_zero, mul_comm]
      exact e
    rw [e']
    exact mem_O_ratOf.1 ((hg τ).1 i i)
  have hgerm : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      germOf y (t hA τ i) = germOf y (t hA' τ i) := fun {y A A'} hA hA' τ i => by
    rw [germOf_eq_iff, unitAt_iff (div_ne_zero (t hA' τ i).ne_zero (t hA τ i).ne_zero), inv_div]
    exact ⟨hreg hA hA' τ i, hreg hA' hA τ i⟩
  choose A hA using fun y : Y.X => S.nonempty y
  refine ⟨fun τ i => show cartierGroup Y.X from ⟨fun y => germOf y (t (hA y) τ i), fun y => ?_⟩,
    fun y => ⟨A y, hA y, t (hA y), fun _ _ => rfl, fun τ i k hik => (hP (hA y) τ).2.2.2 i k i.2 hik,
      fun _ _ => rfl⟩⟩
  obtain ⟨U, B, hy, hB, hU⟩ := S.loc y
  have hBm : ∀ z ∈ U, B ∈ S.S z := fun z hz => (hU z hz B).2 (by rw [Mat.mul_inv hB]; exact Par.one)
  exact ⟨U, hy, t (hBm y hy) τ i, fun z hz => hgerm (hA z) (hBm z hz) τ i⟩

theorem exists_gr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e Y π f₀ S A₀ hT
  obtain ⟨gr, hgr⟩ := exists_div S hT.1
  refine ⟨gr, fun y => ?_⟩
  obtain ⟨A, hA, t, h1, h2, h3⟩ := hgr y
  obtain ⟨φ, f, hf⟩ := hT.2 y A hA
  exact ⟨φ, f, t, (f.tri_iff _ f₀ t).2 ⟨_, hf, h1, h2⟩, h3⟩

end GlobalTheory.ShFam.GradedDiv
