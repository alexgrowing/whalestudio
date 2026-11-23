import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombForm

section Atlas

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def tAtlas (A : FinHolAtlas e X) (h : X ≃ₜ X') : FinHolAtlas e X' where
  n := A.n
  chart j := h.symm.transOpenPartialHomeomorph (A.chart j)
  cover x := (A.cover (h.symm x)).imp fun _ hj => hj
  holo j k := by
    have e₁ : (h.symm.transOpenPartialHomeomorph (A.chart k)) ∘ (h.symm.transOpenPartialHomeomorph (A.chart j)).symm =
        A.chart k ∘ (A.chart j).symm := funext fun y => by simp
    have e₂ : (h.symm.transOpenPartialHomeomorph (A.chart j)).target ∩
        (h.symm.transOpenPartialHomeomorph (A.chart j)).symm ⁻¹' (h.symm.transOpenPartialHomeomorph (A.chart k)).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      ext y; simp
    rw [e₁, e₂]
    exact A.holo j k

theorem tAtlas_symm (A : FinHolAtlas e X) (h : X ≃ₜ X') (j : Fin (tAtlas A h).n) (y : Fin e → ℂ) :
    ((tAtlas A h).chart j).symm y = h ((A.chart j).symm y) := rfl

theorem tAtlas_target (A : FinHolAtlas e X) (h : X ≃ₜ X') (j : Fin (tAtlas A h).n) :
    ((tAtlas A h).chart j).target = (A.chart j).target := rfl

end Atlas

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem isAlgAtlas_tAtlas {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) :
    IsAlgAtlas (tAtlas (M.A a) (I.pt a)) := fun j => by
  obtain ⟨c, hc⟩ := I.alg a j
  refine ⟨c, OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun x => ?_) ?_⟩
  · change (M.A a).chart j ((I.pt a).symm x) = _
    rw [hc]; simp
  · change I.pt a (((M.A a).chart j).symm x) = _
    rw [hc]; simp
  · change (I.pt a).symm ⁻¹' ((M.A a).chart j).source = _
    rw [hc]; ext x; simp

def readFn {e : ℕ} {M : Man e} (I : ManIs M Y) (f : M.Fun) : ∀ σ : F →+* ℂ, Pts Y σ → ℝ :=
  I.ε.piCongrLeft (fun σ => Pts Y σ → ℝ) fun a y => f a ((I.pt a).symm y)

theorem readFn_apply {e : ℕ} {M : Man e} (I : ManIs M Y) (f : M.Fun) (a : Fin (M.n + 1)) (x : M.X a) :
    readFn I f (I.ε a) (I.pt a x) = f a x := by
  rw [readFn, Equiv.piCongrLeft_apply_apply, Homeomorph.symm_apply_apply]

theorem readFn_apply' {e : ℕ} {M : Man e} (I : ManIs M Y) (f : M.Fun) (a : Fin (M.n + 1)) (y : Pts Y (I.ε a)) :
    readFn I f (I.ε a) y = f a ((I.pt a).symm y) := by
  rw [readFn, Equiv.piCongrLeft_apply_apply]

section Met

variable {σ : F →+* ℂ} {Δ : Y.Dv}

theorem pn_pos_of_generatesAt {m : C.Met Y σ Δ} {f : Y.Fn} {y : Pts Y σ} (hf : Δ.GeneratesAt (under y) f)
    (h : PosAt m y) : 0 < C.pn Y σ Δ m (C.cx Y σ f) y := by
  obtain ⟨a, ha, e⟩ := exists_pn_eq (C := C) hf
  rw [e m]
  exact mul_pos ha h

def metWeight (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) : Weight Y.str σ (toLB Δ) where
  isLB := isLB_toLB Δ
  φ c y := -Real.log (C.pn Y σ Δ m (C.cx Y σ (c.1.2 : Y.Fn)⁻¹) y)
  trans i j y hi hj := by
    have hi' : under y ∈ i.1.1 := mem_ptsIn.1 hi
    have hj' : under y ∈ j.1.1 := mem_ptsIn.1 hj
    have hg : genericPoint Y.X ∈ (toLB Δ).U i ⊓ (toLB Δ).U j := ⟨i.2.1, j.2.1⟩
    have hu : UnitAt (under y) ((i.1.2 : Y.Fn) / (j.1.2 : Y.Fn)) := (j.2.2 _ hj').iff_unitAt.1 (i.2.2 _ hi')
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 (i.2.2 _ hi')
    have hgv : gv Y.str σ (toLB Δ) i j y = ratVal ((i.1.2 : Y.Fn) / (j.1.2 : Y.Fn)) y := by
      rw [← fnOf_toLB_g i j hg, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩)]
      rfl
    have e₁ : ((j.1.2 : Y.Fn))⁻¹ = ((i.1.2 : Y.Fn) / (j.1.2 : Y.Fn)) * ((i.1.2 : Y.Fn))⁻¹ := by
      field_simp
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm y)
    have hr : 0 < ‖ratVal ((i.1.2 : Y.Fn) / (j.1.2 : Y.Fn)) y‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    show -Real.log (C.pn Y σ Δ m (C.cx Y σ (j.1.2 : Y.Fn)⁻¹) y) =
      -Real.log (C.pn Y σ Δ m (C.cx Y σ (i.1.2 : Y.Fn)⁻¹) y) - Real.log (‖gv Y.str σ (toLB Δ) i j y‖ ^ 2)
    rw [e₁, C.pn_mul Y σ Δ m _ _ y hu.regAt hgen.regularAt, hgv, Real.log_mul hr.ne' hp.ne']
    ring

theorem metWeight_φ (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (c : (toLB Δ).ι) (y : Pts Y σ) :
    (metWeight Δ m hm).φ c y = -Real.log (C.pn Y σ Δ m (C.cx Y σ (c.1.2 : Y.Fn)⁻¹) y) := rfl

theorem IsPot.pullback_symm {X : Type} [TopologicalSpace X] {m : C.Met Y σ Δ} {h : X ≃ₜ Pts Y σ} {Q : LocPot X}
    (hQ : IsPot h m Q) : IsPot id m (Q.pullback h.symm h.symm.continuous) := fun x => by
  obtain ⟨f, hf⟩ := hQ (h.symm x)
  refine ⟨f, fun y hy => ?_⟩
  have := hf (h.symm y) hy
  simpa [LocPot.pullback] using this

end Met

end GlobalTheory.Mean4O.CombForm
