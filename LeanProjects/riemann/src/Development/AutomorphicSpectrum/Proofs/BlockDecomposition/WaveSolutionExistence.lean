import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveAll

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun h continuous_const

theorem mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  have h : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact left_ne_zero_of_mul_eq_one h2

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr {S : Set (Mat n)} (hS : IsOpen S) {f f' : Mat n → V} (h : Set.EqOn f f' S) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') S := by
  intro x hx
  have h' : f =ᶠ[𝓝 x] f' := Filter.eventuallyEq_of_mem (hS.mem_nhds hx) h
  simp only [Rd, h'.fderiv_eq]

theorem Eu_congr {S : Set (Mat n)} (hS : IsOpen S) {f f' : Mat n → V} (h : Set.EqOn f f' S) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') S := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_congr hS h _ hx]

theorem Epow_congr {S : Set (Mat n)} (hS : IsOpen S) {f f' : Mat n → V} (h : Set.EqOn f f' S) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b f) (Epow s m a b f') S := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab, h hx]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => Eu_congr hS (ih c b) s a c hx

theorem gel_congr {S : Set (Mat n)} (hS : IsOpen S) {f f' : Mat n → V} (h : Set.EqOn f f' S) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') S := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => Epow_congr hS h s m a a hx

theorem Om_congr {S : Set (Mat n)} (hS : IsOpen S) {f f' : Mat n → V} (h : Set.EqOn f f' S) :
    Set.EqOn (Om f) (Om f') S := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_congr hS h _ _ hx]

theorem Rd_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (X : Mat n) :
    Set.EqOn (Rd X (f - f')) (Rd X f - Rd X f') (GLs n) := by
  intro x hx
  have h1 : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ f' x :=
    (hf'.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  have h3 : fderiv ℝ (f - f') x = fderiv ℝ f x - fderiv ℝ f' x := (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
  simp only [Rd, Pi.sub_apply, h3]
  rfl

theorem Eu_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (f - f')) (Eu s a b f - Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Rd_sub hf hf' _ hx, smul_sub, smul_add]
  abel

theorem Eu_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := ((hR n).1 V f hf).1
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth hR (ih c b) s a c

theorem Epow_sub (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f - f')) (Epow s m a b f - Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr isOpen_GLs (ih c b) s a c hx]
    exact Eu_sub (Epow_smooth hR hf s m c b) (Epow_smooth hR hf' s m c b) s a c hx

theorem gel_sub (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f - f')) (gel s m f - gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_sub hR hf hf' s m a a hx

theorem Om_sub (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f - f')) (Om f - Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, gel_sub hR hf hf' _ _ hx, smul_sub, smul_add]
  abel

end Ops

theorem wave_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {g : Mat n} (hg : g ∈ GLs n) :
    ContDiff ℝ ∞ fun s => u s g := by
  have h : ContDiffOn ℝ ∞ (Function.uncurry u ∘ fun s : ℝ => (s, g)) Set.univ :=
    hu.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun s _ => ⟨trivial, hg⟩
  exact contDiffOn_univ.1 h

theorem wave_sub (hR : RCalc) {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E (u - v) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · exact hu.1.sub hv.1
  · exact (hu.2.1 t).1.sub (hv.2.1 t).1
  · intro g hg k
    simp only [Pi.sub_apply, (hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_sub]
  · have h1 := (wave_line hu hg).contDiffAt (x := t)
    have h2 := (wave_line hv hg).contDiffAt (x := t)
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, iteratedDeriv_sub (h1.of_le (WithTop.coe_le_coe.2 le_top)) (h2.of_le (WithTop.coe_le_coe.2 le_top)),
      hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_sub hR (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 := ((wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 := ((wave_line hv hg).differentiable (by simp)).differentiableAt
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, deriv_sub h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, sub_zero]

def cut (R : ℝ) (y : Mat n) : ℝ := Real.smoothTransition (R + 1 - lg y)

theorem cut_smooth (hL : LgFacts) (R : ℝ) : ContDiffOn ℝ ∞ (cut R : Mat n → ℝ) (GLs n) := by
  have h : ContDiffOn ℝ ∞ lg (GLs n) := (hL n).2.2.2.1
  exact Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_const.sub h)

theorem cut_eq_one {R : ℝ} {y : Mat n} (h : lg y ≤ R) : cut R y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cut_eq_zero {R : ℝ} {y : Mat n} (h : R + 1 < lg y) : cut R y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem lg_mul_unitary (hL : LgFacts) {x : Mat n} (hx : x ∈ GLs n) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    lg (x * k.1) = lg x := by
  have h := (hL n).2.2.1 x hx 1 k
  simpa using h

def cutSec {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (R : ℝ) (f : Mat n → V) : Mat n → V :=
  fun y => cut R y • f y

theorem cutSec_mem (hL : LgFacts) {E : KMod n} {f : Mat n → E.V} (hf : f ∈ CE E) (R : ℝ) : cutSec R f ∈ CE E := by
  refine ⟨(cut_smooth hL R).smul hf.1, fun g hg k => ?_⟩
  simp only [cutSec, cut, lg_mul_unitary hL hg k, hf.2 g hg k]
  exact (ContinuousLinearMap.map_smul_of_tower _ _ _).symm

theorem cutSec_cpt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (R : ℝ) (f : Mat n → V) : Cpt (cutSec R f) :=
  ⟨R + 1, fun y _ hy => by simp [cutSec, cut_eq_zero hy]⟩

theorem glue (hL : LgFacts) {E : KMod n} (c : ℝ) (U : ℕ → ℝ → Mat n → E.V) (hU : ∀ N, IsWave E (U N))
    (hst : ∀ (N M : ℕ) (t : ℝ), ∀ x ∈ GLs n, lg x + c * (1 + |t|) ≤ N → lg x + c * (1 + |t|) ≤ M → U N t x = U M t x) :
    ∃ u, IsWave E u ∧ ∀ (N : ℕ) (t : ℝ), ∀ x ∈ GLs n, lg x + c * (1 + |t|) ≤ N → u t x = U N t x := by
  set l : ℝ × Mat n → ℝ := fun p => lg p.2 + c * (1 + |p.1|) with hl
  obtain ⟨u, hud⟩ : ∃ u : ℝ → Mat n → E.V, ∀ t x, u t x = U ⌈l (t, x)⌉₊ t x := ⟨_, fun _ _ => rfl⟩
  have hu : ∀ (N : ℕ) (t : ℝ), ∀ x ∈ GLs n, l (t, x) ≤ N → u t x = U N t x :=
    fun N t x hx h => (hud t x).trans (hst _ _ t x hx (Nat.le_ceil _) h)
  have hlc : ContinuousOn l (Set.univ ×ˢ GLs n) := by
    have h1 : ContinuousOn (fun p : ℝ × Mat n => lg p.2) (Set.univ ×ˢ GLs n) :=
      (hL n).2.2.2.1.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2
    exact h1.add (by fun_prop)
  let W : ℕ → Set (ℝ × Mat n) := fun N => (Set.univ ×ˢ GLs n) ∩ l ⁻¹' Set.Iio (N : ℝ)
  have hWo : ∀ N, IsOpen (W N) := fun N =>
    hlc.isOpen_inter_preimage (isOpen_univ.prod isOpen_GLs) isOpen_Iio
  have hWm : ∀ t, ∀ x ∈ GLs n, (t, x) ∈ W (⌈l (t, x)⌉₊ + 1) := fun t x hx =>
    ⟨⟨trivial, hx⟩, by
      have := Nat.le_ceil (l (t, x))
      simp only [Set.mem_preimage, Set.mem_Iio]
      push_cast
      linarith⟩
  have hWu : ∀ N, ∀ p ∈ W N, Function.uncurry u p = Function.uncurry (U N) p := fun N p hp =>
    hu N p.1 p.2 hp.1.2 (le_of_lt hp.2)
  have hsm : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n) := by
    rintro ⟨t, x⟩ ⟨-, hx⟩
    have hm := hWm t x hx
    refine ((hU _).1 (t, x) ⟨trivial, hx⟩).congr_of_eventuallyEq ?_ (hWu _ _ hm)
    exact Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds ((hWo _).mem_nhds hm)) fun p hp => hWu _ p hp

  have hSo : ∀ (N : ℕ) (t : ℝ), IsOpen ((fun x : Mat n => (t, x)) ⁻¹' W N) := fun N t =>
    (hWo N).preimage (by fun_prop)
  have hTo : ∀ (N : ℕ) (g : Mat n), IsOpen ((fun s : ℝ => (s, g)) ⁻¹' W N) := fun N g =>
    (hWo N).preimage (by fun_prop)
  have hline : ∀ (t : ℝ), ∀ g ∈ GLs n, (fun s => u s g) =ᶠ[𝓝 t] fun s => U (⌈l (t, g)⌉₊ + 1) s g := fun t g hg =>
    Filter.eventuallyEq_of_mem ((hTo _ g).mem_nhds (hWm t g hg)) fun s hs => hWu _ (s, g) hs
  refine ⟨u, ⟨hsm, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩, fun N t x hx h => hu N t x hx h⟩
  · have h : ContDiffOn ℝ ∞ (Function.uncurry u ∘ fun x : Mat n => (t, x)) (GLs n) :=
      hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun x hx => ⟨trivial, hx⟩
    exact h
  · intro g hg k
    have hk : g * k.1 ∈ GLs n := mul_mem_GLs hg (unitary_mem_GLs k)
    have e : l (t, g * k.1) = l (t, g) := by simp only [hl, lg_mul_unitary hL hg k]
    rw [hu _ t g hg (Nat.le_ceil _), hu ⌈l (t, g)⌉₊ t _ hk (by rw [e]; exact Nat.le_ceil _)]
    exact ((hU _).2.1 t).2 g hg k
  · have hS := hSo (⌈l (t, g)⌉₊ + 1) t
    have h1 : Set.EqOn (u t) (U (⌈l (t, g)⌉₊ + 1) t) ((fun x : Mat n => (t, x)) ⁻¹' W (⌈l (t, g)⌉₊ + 1)) :=
      fun x hx => hWu _ (t, x) hx
    rw [(hline t g hg).iteratedDeriv_eq, (hU _).2.2.1 t g hg]
    exact (Om_congr hS h1 (hWm t g hg)).symm
  · rw [(hline 0 g hg).deriv_eq]
    exact (hU _).2.2.2 g hg

theorem asmEx : AsmEx := by
  intro hL hR hS hC n E f hf
  obtain ⟨c₀, hc₀⟩ := hS n
  set c := max c₀ 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have speed : ∀ u, IsWave E u → ∀ t : ℝ, ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ c * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0 := fun u hu t x hx h =>
    hc₀ E u hu t x hx fun y hy hly => h y hy
      (hly.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hex : ∀ N : ℕ, ∃ u, IsWave E u ∧ ∀ g ∈ GLs n, u 0 g = cutSec (N : ℝ) f g := fun N =>
    hC n E _ (cutSec_mem hL hf N) (cutSec_cpt _ f)
  choose U hU hU0 using hex
  have hst : ∀ (N M : ℕ) (t : ℝ), ∀ x ∈ GLs n, lg x + c * (1 + |t|) ≤ N → lg x + c * (1 + |t|) ≤ M →
      U N t x = U M t x := by
    intro N M t x hx hN hM
    refine sub_eq_zero.1 (speed _ (wave_sub hR (hU N) (hU M)) t x hx fun y hy hly => ?_)
    have hxy := mul_mem_GLs hx hy
    have hsub := (hL n).1 x hx y hy
    simp only [Pi.sub_apply, hU0 N _ hxy, hU0 M _ hxy, cutSec]
    rw [cut_eq_one (by linarith), cut_eq_one (by linarith), sub_self]
  obtain ⟨u, hu, hUu⟩ := glue hL c U hU hst
  refine ⟨u, hu, fun g hg => ?_⟩
  have hlg : lg g + c * (1 + |(0 : ℝ)|) ≤ (⌈lg g + c * (1 + |(0 : ℝ)|)⌉₊ : ℕ) := Nat.le_ceil _
  rw [hUu _ 0 g hg hlg, hU0 _ g hg]
  simp only [abs_zero, add_zero, mul_one] at hlg
  simp only [cutSec]
  rw [cut_eq_one (by simp only [abs_zero, add_zero, mul_one]; linarith), one_smul]

end GlobalTheory.CompanionTheory.WaveAll
