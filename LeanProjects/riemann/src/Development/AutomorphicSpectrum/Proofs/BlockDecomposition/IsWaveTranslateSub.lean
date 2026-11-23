import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveInv

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem gls_mul {h x : Mat n} (hh : h ∈ GLs n) (hx : x ∈ GLs n) : h * x ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hh hx

theorem gls_val (v : G n) : v.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero

theorem contDiff_mulLeft (h : Mat n) : ContDiff ℝ ∞ (fun x : Mat n => h * x) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ h)).contDiff

theorem contDiffOn_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {h : Mat n} (hh : h ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (h * y)) (GLs n) :=
  hf.comp (contDiff_mulLeft h).contDiffOn fun _ hy => gls_mul hh hy

theorem gel_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    gel s m (fun y => f₁ y - f₂ y) g = gel s m f₁ g - gel s m f₂ g := by
  have hP : ContDiffOn ℝ ∞ (fun y => (f₁ y, f₂ y)) (GLs n) := h₁.prodMk h₂
  have c := ((hG n (V × V) V s m (fun y => (f₁ y, f₂ y)) hP).2 g hg).2.2
  have a : gel s m f₁ g = _ := c (ContinuousLinearMap.fst ℂ V V)
  have b : gel s m f₂ g = _ := c (ContinuousLinearMap.snd ℂ V V)
  have d : gel s m (fun y => f₁ y - f₂ y) g = _ :=
    c (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  rw [d, a, b]
  rfl

theorem Om_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => f₁ y - f₂ y) g = Om f₁ g - Om f₂ g := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_sub hG _ _ h₁ h₂ hg]
  module

theorem Om_translate (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {h g : Mat n} (hh : h ∈ GLs n) (hg : g ∈ GLs n) :
    Om (fun y => f (h * y)) g = Om f (h * g) := by
  have c := fun s m => (((hG n V V s m f hf).2 g hg).2.1 h hh).1
  simp only [Om, Pi.smul_apply, Pi.add_apply, c]

theorem contDiff_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {y : Mat n} (hy : y ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s y) := by
  have hl : ContDiff ℝ ∞ (fun s : ℝ => (s, y)) := contDiff_id.prodMk contDiff_const
  have := hu.1.comp hl.contDiffOn (s := Set.univ) fun s _ => ⟨Set.mem_univ _, hy⟩
  exact contDiffOn_univ.mp this

theorem isWave_translate_sub (hG : GelComm) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u)
    {h : Mat n} (hh : h ∈ GLs n) : IsWave E (fun t x => u t (h * x) - u t x) := by
  have hs : ∀ t, ContDiffOn ℝ ∞ (u t) (GLs n) := fun t => (hu.2.1 t).1
  refine ⟨?_, fun t => ⟨(contDiffOn_translate (hs t) hh).sub (hs t), fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · have hmap : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1, h * p.2)) :=
      contDiff_fst.prodMk ((contDiff_mulLeft h).comp contDiff_snd)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Function.uncurry u (p.1, h * p.2)) (Set.univ ×ˢ GLs n) :=
      hu.1.comp hmap.contDiffOn fun p hp => ⟨Set.mem_univ _, gls_mul hh hp.2⟩
    exact h1.sub hu.1
  · have e₁ := (hu.2.1 t).2 (h * g) (gls_mul hh hg) k
    have e₂ := (hu.2.1 t).2 g hg k
    simp only [← mul_assoc, e₁, e₂, map_sub]
  · have hc₁ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s (h * g)) t :=
      (contDiff_infty.mp (contDiff_line hu (gls_mul hh hg)) 2).contDiffAt
    have hc₂ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s g) t :=
      (contDiff_infty.mp (contDiff_line hu hg) 2).contDiffAt
    rw [iteratedDeriv_fun_sub hc₁ hc₂, hu.2.2.1 t _ (gls_mul hh hg), hu.2.2.1 t _ hg,
      Om_sub hG (contDiffOn_translate (hs t) hh) (hs t) hg, Om_translate hG (hs t) hh hg]
  · have d₁ : DifferentiableAt ℝ (fun s => u s (h * g)) 0 :=
      ((contDiff_line hu (gls_mul hh hg)).differentiable (by simp)).differentiableAt
    have d₂ : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((contDiff_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_sub d₁ d₂, hu.2.2.2 _ (gls_mul hh hg), hu.2.2.2 _ hg, sub_zero]

theorem waveN : PositivityTheory.RgBcC.VC.WaveN := by
  intro hEx hSp hG n E W₁ W₂ f hf hN
  obtain ⟨u, hu, h0⟩ := hEx n E f hf
  refine ⟨u, hu, h0, fun t v hv x hx => ?_⟩
  obtain ⟨c, hc⟩ := hSp n
  have hvG := gls_val v
  have hz := hc E _ (isWave_translate_sub hG hu hvG) t x hx fun y hy _ => by
    have hxy := gls_mul hx hy
    rw [h0 _ (gls_mul hvG hxy), h0 _ hxy, hN v hv _ hxy, sub_self]
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.WaveInv
