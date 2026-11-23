import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (X : Mat n) : EqOn (Rd X f) (Rd X f') (GLs n) := by
  intro g hg
  have he : f =ᶠ[nhds g] f' := Filter.eventually_of_mem ((isOpen_GLs n).mem_nhds hg) h
  simp only [Rd, he.fderiv_eq]

theorem eu_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_congr h _ hg]

theorem epow_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b, EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | succ m ih =>
    intro a b g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (ih c b) s a c hg

theorem gel_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem rd_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf

end Ops

theorem gel_sum (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type} [Fintype ι]
    (F : ι → Mat n → V) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    ∀ g ∈ GLs n, gel s m (fun y => ∑ i, F i y) g = ∑ i, gel s m (F i) g := by
  classical
  intro g hg
  let Φ : Mat n → (ι → V) := fun y i => F i y
  have hΦ : ContDiffOn ℝ ∞ Φ (GLs n) := contDiffOn_pi.2 hF
  have hsum := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (∑ i, ContinuousLinearMap.proj (R := ℂ) i)
  have hproj : ∀ i, gel s m (F i) g = gel s m Φ g i := by
    intro i
    have := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (ContinuousLinearMap.proj (R := ℂ) i)
    simpa [Φ] using this
  have e : (fun y => ∑ i, F i y) = fun y => (∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => V) i) (Φ y) := by
    funext y; simp [Φ]
  rw [e, hsum]
  simp [hproj]

theorem gel_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (_h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ x ∈ GLs n, gel s m (DC ε Fr f) x = DC ε Fr (gel s m f) x := by
  intro x hx
  have hR : ∀ p, ContDiffOn ℝ ∞ (Rd (hb p) f) (GLs n) := fun p => rd_smooth hf _
  have hD : ∀ p, ContDiffOn ℝ ∞ (fun y => fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hGp : ∀ p, ContDiffOn ℝ ∞ (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => (hR p).add (hD p)
  have hFp : ∀ p, ContDiffOn ℝ ∞ (fun y => ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y))) (GLs n) :=
    fun p => ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (hGp p)
  have e1 : DC ε Fr f = fun y => ∑ p, ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) := rfl
  rw [e1, gel_sum hG _ hFp s m x hx]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [((hG n E.V E.V s m _ (hGp p)).2 x hx).2.2 (ε (hb p))]
  congr 1
  have h2 := gel_sum hG (fun (i : Fin 2) y => if i = 0 then Rd (hb p) f y else fderiv ℝ Fr 1 (hb p) (f y))
    (fun i => by fin_cases i <;> simp [hR p, hD p]) s m x hx
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false] at h2
  have h2' : gel s m (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) x =
      gel s m (Rd (hb p) f) x + gel s m (fun y => fderiv ℝ Fr 1 (hb p) (f y)) x := by
    simpa using h2
  rw [h2', ((hG n E.V E.V s m f hf).2 x hx).2.2 (fderiv ℝ Fr 1 (hb p)), ((hG n E.V E.V s m f hf).2 x hx).1 (hb p)]

theorem zopDC : ZopDC := by
  intro hG n lam E Fr ε ι S Γ T hCx h hh w
  induction w with
  | nil => exact ⟨hh, fun x _ => rfl⟩
  | cons p w ih =>
    obtain ⟨ihs, ihc⟩ := ih
    refine ⟨(hG n E.V E.V p.1 p.2 _ ihs).1, fun x hx => ?_⟩
    show gel p.1 p.2 (zOp w (DC ε Fr h)) x = DC ε Fr (gel p.1 p.2 (zOp w h)) x
    rw [gel_congr (fun y hy => ihc y hy) p.1 p.2 hx]
    exact gel_DC hG hCx (zOp w h) ihs p.1 p.2 x hx

end PositivityTheory.RgBcC.LfSt.ChainOf2
