import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordL2LaplacianBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobOpsPf

open GlobalTheory.CompanionTheory.RCalc (Rd_congr Rd_add Rd_smul Rd_contDiffOn differentiableAt_of_smooth gel_contDiffOn Rd_gel gel_right
  gel_post fderiv_comp_clm fderiv_post mulR mapsTo_mulR)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth Rw_append Rd_sum_cf)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_add (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (Rw w (f + f')) (Rw w f + Rw w f') (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_add (bs p) (Rw_smooth w hf) (Rw_smooth w hf') hx)

theorem Rw_smul (w : List (Bool × Fin n × Fin n)) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (c • f)) (c • Rw w f) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_smul c (bs p) (Rw_smooth w hf) hx)

theorem Om_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Om f) (GLs n) :=
  ((gel_contDiffOn true 2 hf).add (gel_contDiffOn false 2 hf)).const_smul (2 : ℂ)

theorem Rd_Om (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Om f) g = Om (Rd X f) g := by
  have h1 := gel_contDiffOn true 2 hf
  have h2 := gel_contDiffOn false 2 hf
  have h3 : ContDiffOn ℝ ∞ (gel true 2 f + gel false 2 f) (GLs n) := h1.add h2
  have e1 := Rd_smul (2 : ℂ) X h3 hg
  have e2 := Rd_add X h1 h2 hg
  simp only [Pi.smul_apply, Pi.add_apply] at e1 e2
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [e1, e2, Rd_gel X true 2 hf hg, Rd_gel X false 2 hf hg]

theorem Rw_Om (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (Om f)) (Om (Rw w f)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_Om (bs p) (Rw_smooth w hf) hx)

theorem Rd_translate (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => f (y * x)) g = Rd (x⁻¹ * X * x) f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hd := differentiableAt_of_smooth hf (mapsTo_mulR hx hg)
  have e : g * x * (x⁻¹ * X * x) = g * X * x := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have := fderiv_comp_clm (mulR x) hd (g * X)
  simp only [Rd, e]
  exact this

theorem Rd_post (X : Mat n) (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) :=
  fderiv_post A (differentiableAt_of_smooth hf hg) _

theorem post_smooth (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => A (f y)) (GLs n) :=
  (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf

theorem Rw_post (w : List (Bool × Fin n × Fin n)) (A : V →L[ℂ] V) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (Rw w (fun y => A (f y))) (fun y => A (Rw w f y)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_post (bs p) A (Rw_smooth w hf) hx)

theorem Om_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => A (f y)) g = A (Om f g) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_post A _ _ hf hg, map_smul, map_add]

theorem Om_translate {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Om (fun y => f (y * x)) g = Om f (g * x) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_right _ _ hx hf hg]

theorem translate_smooth {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * x)) (GLs n) :=
  hf.comp (mulR x).contDiff.contDiffOn (mapsTo_mulR hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem val_mem (y : G n) : y.val ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.ByParts.val_mem_GLs y

theorem sob_congr {f h : Mat n → V} (hf : Sob μ f) (e : Set.EqOn f h (GLs n)) : Sob μ h :=
  ⟨hf.1.congr fun _ hx => (e hx).symm, fun w =>
    MemLp.ae_eq (ae_of_all _ fun y => Rw_congr w e (val_mem y)) (hf.2 w)⟩

theorem sob_add {f h : Mat n → V} (hf : Sob μ f) (hh : Sob μ h) : Sob μ (f + h) :=
  ⟨hf.1.add hh.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_add w hf.1 hh.1 (val_mem y)).symm)
    ((hf.2 w).add (hh.2 w))⟩

theorem sob_smul (c : ℂ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (c • f) :=
  ⟨hf.1.const_smul c, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_smul w c hf.1 (val_mem y)).symm)
    ((hf.2 w).const_smul c)⟩

theorem sob_zero {f : Mat n → V} (hf : Sob μ f) : Sob μ (0 : Mat n → V) := by
  simpa using sob_smul (0 : ℂ) hf

theorem sob_sum {ι : Type} (s : Finset ι) {f₀ : Mat n → V} (h₀ : Sob μ f₀) {F : ι → Mat n → V}
    (hF : ∀ i, Sob μ (F i)) : Sob μ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sob_zero h₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sob_add (hF a) ih

theorem sob_Rw (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rw w f) :=
  ⟨Rw_smooth w hf.1, fun w' => by rw [Rw_append]; exact hf.2 _⟩

theorem sob_bs (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd (bs p) f) :=
  sob_Rw [p] hf

theorem sob_Rd (X : Mat n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd X f) := by
  refine sob_congr (f := ∑ p : Bool × Fin n × Fin n, ((GlobalTheory.CompanionTheory.SobSecK.cf X p : ℝ) : ℂ) • Rd (bs p) f)
    (sob_sum _ hf fun p => sob_smul _ (sob_bs p hf)) fun g _ => ?_
  rw [Rd_sum_cf X f g]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem sob_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Eu s a b f) :=
  sob_smul _ (sob_add (sob_Rd _ hf) (sob_smul _ (sob_Rd _ hf)))

theorem sob_Epow (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : ∀ a b, Sob μ (Epow s m a b f) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simpa [Epow, hab] using sob_zero hf
  | succ m ih =>
    intro a b
    exact sob_sum _ hf fun c => sob_Eu s a c (ih c b)

theorem sob_gel (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (gel s m f) :=
  sob_sum _ hf fun a => sob_Epow s m hf a a

theorem sob_Om {f : Mat n → V} (hf : Sob μ f) : Sob μ (Om f) :=
  sob_smul _ (sob_add (sob_gel _ _ hf) (sob_gel _ _ hf))

theorem sob_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : Sob μ f) : Sob μ (fun y => A (f y)) :=
  ⟨post_smooth A hf.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_post w A hf.1 (val_mem y)).symm)
    (A.comp_memLp' (hf.2 w))⟩

variable [BorelSpace (G n)] [μ.IsHaarMeasure]

theorem memLp_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : MemLp (fun y : G n => F y.val) 2 μ) :
    MemLp (fun y : G n => F (y.val * h.val)) 2 μ := by
  haveI := (hU n μ).1
  exact hF.comp_measurePreserving (measurePreserving_mul_right μ h)

theorem translate_memLp (hU : Unimod) (h : G n) (w : List (Bool × Fin n × Fin n)) :
    ∀ F : Mat n → V, Sob μ F → MemLp (fun y : G n => Rw w (fun z => F (z * h.val)) y.val) 2 μ := by
  induction w using List.reverseRecOn with
  | nil => exact fun F hF => memLp_translate hU h (hF.2 [])
  | append_singleton w p ih =>
    intro F hF
    rw [← Rw_append [p] w]
    have e : Set.EqOn (Rw [p] fun z => F (z * h.val)) (fun z => Rd (h.val⁻¹ * bs p * h.val) F (z * h.val)) (GLs n) :=
      fun g hg => Rd_translate (bs p) (val_mem h) hF.1 hg
    exact MemLp.ae_eq (ae_of_all _ fun y => (Rw_congr w e (val_mem y)).symm) (ih _ (sob_Rd _ hF))

theorem sob_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : Sob μ F) : Sob μ (fun y => F (y * h.val)) :=
  ⟨translate_smooth (val_mem h) hF.1, fun w => translate_memLp hU h w F hF⟩

end Sob

theorem sobOps : SobOps := by
  intro n _ _ μ _ V _ _ _ hU _ f hf
  refine ⟨sob_Om hf, fun w => sob_Rw w hf, fun w g hg => Rw_Om w hf.1 hg, fun a f' hf' => ⟨sob_add (sob_smul a hf) hf', ?_⟩,
    fun h A => ⟨sob_post A (sob_translate hU h hf), fun g hg => ?_⟩⟩
  · intro g hg
    have hs : ContDiffOn ℝ ∞ (a • f) (GLs n) := hf.1.const_smul a
    have e1 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_add hs hf'.1 hg
    have e2 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_smul a hf.1 hg
    simp only [Pi.add_apply, Pi.smul_apply] at e1 e2
    rw [e1, e2]
  · rw [Om_post A (translate_smooth (val_mem h) hf.1) hg, Om_translate (val_mem h) hf.1 hg]

end GlobalTheory.CompanionTheory.SobOpsPf
