import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory
namespace CurveProductSmooth

variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)

def JointlySmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → K) : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E), ContDiff ℝ ∞ g →
    ∀ l : List (P × (F → ℝ)), (∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) →
      ContDiff ℝ ∞ fun x : F => ρ (l.map fun a => e a.1 (a.2 x)).prod (Φ (g x))

variable {ρ A e}

theorem JointlySmooth.translate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    JointlySmooth ρ A e fun t => ρ (m.map fun a => e a.1 (a.2 t)).prod (Φ t) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map] at h1
  exact h1

theorem JointlySmooth.extra {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A)
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F → E) (hg : ContDiff ℝ ∞ g)
    (l : List (P × (F → ℝ))) (hl : ∀ a ∈ l, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    ContDiff ℝ ∞ fun y : F × ℝ =>
      ρ (l.map fun a => e a.1 (a.2 y.1)).prod (ρ (e p y.2) (Φ (g y.1))) := by
  have h1 := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst)
    ((l.map fun a => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · obtain rfl := List.mem_singleton.1 ha
      exact ⟨hp, contDiff_snd⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
  exact h1

theorem JointlySmooth.deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have h1 := h.extra hp F g hg l hl
  have h0 := h.extra hp F g hg [] (by simp)
  simp only [List.map_nil, List.prod_nil, map_one, one_apply_eq_self] at h0
  have hd : ∀ x : F, DifferentiableAt ℝ (fun r : ℝ => ρ (e p r) (Φ (g x))) 0 := fun x =>
    ((h0.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun r : ℝ => (x, r))).differentiable
      (by simp)) 0
  have h2 : ContDiff ℝ ∞ fun x : F => fderiv ℝ (fun r : ℝ =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) 0 :=
    ContDiff.fderiv (f := fun (x : F) (r : ℝ) =>
      ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x)))) (g := fun _ => (0 : ℝ))
      (m := ∞) h1 contDiff_const (by simp)
  have h3 := h2.clm_apply (contDiff_const (c := (1 : ℝ)))
  convert h3 using 2 with x
  have h4 := ((ρ (l.map fun a => e a.1 (a.2 x)).prod).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hd x).hasDerivAt
  exact h4.deriv.symm

theorem JointlySmooth.foldr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => _root_.deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    exact (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)).deriv (hl p List.mem_cons_self)

end CurveProductSmooth

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem contDiff_prod_ofFn_apply_of_jointlySmooth {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {g : (Fin k → ℝ) → E}
    (hg : ContDiff ℝ ∞ g) (ps : Fin k → P) (hps : ∀ i, ps i ∈ A) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (Φ (g t)) := by
  have h1 := h (Fin k → ℝ) g hg (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
  simpa [List.map_ofFn, Function.comp_def] using h1

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem deriv_continuousLinearMap_comp_eq (T : K →L[ℂ] K) (f : ℝ → K) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun r => T (f r)) 0 = T (deriv f 0) :=
  ((T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) {p : P} (hp : p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t => deriv (fun r : ℝ => ρ (e p r) (Φ t)) 0 := by
  intro F _ _ g hg l hl
  have hf : ∀ y : E, ContDiff ℝ ∞ fun r : ℝ => ρ (e p r) (Φ y) := fun y => by
    simpa using h ℝ (fun _ => y) contDiff_const [(p, id)] (by simp [hp, contDiff_id])
  let H : F × ℝ → K := fun z =>
    ρ (((l.map fun a : P × (F → ℝ) => (a.1, a.2 ∘ Prod.fst)) ++ [(p, Prod.snd)]).map
      fun a : P × (F × ℝ → ℝ) => e a.1 (a.2 z)).prod
      (Φ (g z.1))
  have hH : ContDiff ℝ ∞ H := h (F × ℝ) (g ∘ Prod.fst) (hg.comp contDiff_fst) _ (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hl b hb).1, (hl b hb).2.comp contDiff_fst⟩
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hp, contDiff_snd⟩)
  have hHx : ∀ x r, H (x, r) = ρ (l.map fun a => e a.1 (a.2 x)).prod (ρ (e p r) (Φ (g x))) := by
    intro x r
    simp [H, List.map_append, List.map_map, Function.comp_def, map_mul]
  have hder : ∀ x, ρ (l.map fun a => e a.1 (a.2 x)).prod (deriv (fun r : ℝ => ρ (e p r) (Φ (g x))) 0)
      = fderiv ℝ H (x, 0) (0, 1) := by
    intro x
    rw [← deriv_continuousLinearMap_comp_eq _ _ ((hf (g x)).differentiable (by simp)).differentiableAt]
    have h2 : HasDerivAt (fun r : ℝ => H (x, r)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    rw [← h2.deriv]
    simp only [hHx]
  have hfin : ContDiff ℝ ∞ fun x : F => fderiv ℝ H (x, 0) (0, 1) :=
    ((contDiff_infty_iff_fderiv.1 hH).2.comp (contDiff_id.prodMk contDiff_const)).clm_apply
      contDiff_const
  convert hfin using 1
  funext x
  exact hder x

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_const' {v : K}
    (hv : ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e (fun _ : E => v) := by
  intro F _ _ g _ l hl
  have h1 := hv l.length (fun i => l[i].1) (fun i => (hl _ (List.getElem_mem _)).1)
  have h2 : ContDiff ℝ ∞ fun x : F => fun i : Fin l.length => l[i].2 x :=
    contDiff_pi.2 fun i => (hl _ (List.getElem_mem _)).2
  have h3 := h1.comp h2
  convert h3 using 1
  funext x
  simp only [Function.comp_apply]
  have hlist : (l.map fun a : P × (F → ℝ) => e a.1 (a.2 x)) =
      List.ofFn fun i : Fin l.length => e l[i].1 (l[i].2 x) :=
    List.ext_getElem (by simp) (by simp)
  rw [hlist]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_prod_map_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun y => ρ (m.map fun a => e a.1 (a.2 y)).prod (Φ y) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  convert h1 using 1
  funext x
  simp [List.map_append, List.prod_append, map_mul, List.map_map, Function.comp_def]

open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G) in
variable {ρ A e} in
private theorem jointlySmooth_foldr_deriv_action {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → K} (h : _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e Φ) (l : List P) (hl : ∀ p ∈ l, p ∈ A) :
    _root_.GlobalTheory.CurveProductSmooth.JointlySmooth ρ A e fun t =>
      l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (Φ t) := by
  induction l with
  | nil => exact h
  | cons q l ih =>
    exact jointlySmooth_deriv_action (ih fun p hp => hl p (List.mem_cons_of_mem _ hp)) (hl q (by simp))

open scoped ContDiff in

theorem _root_.GlobalTheory.smooth_along_curve_products_stable : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  intro G _ K _ _ _ ρ P A e v hv
  refine ⟨fun p hp k ps hps => ?_, fun m qs r hqs k ps hps => ?_, fun l hl k ps hps => ?_⟩
  · exact contDiff_prod_ofFn_apply_of_jointlySmooth
      (jointlySmooth_deriv_action (jointlySmooth_const' hv (E := ℝ)) hp) (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := ℝ))
      (List.ofFn fun i => (qs i, fun _ : ℝ => r i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hqs i, contDiff_const⟩)
    simpa [List.map_ofFn, Function.comp_def] using
      contDiff_prod_ofFn_apply_of_jointlySmooth h1 (g := fun _ => 0) contDiff_const ps hps
  · have h1 := jointlySmooth_prod_map_action (jointlySmooth_const' hv (E := Fin k → ℝ))
      (List.ofFn fun i => (ps i, fun t : Fin k → ℝ => t i)) (by
        intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨hps i, contDiff_apply ℝ ℝ i⟩)
    have h2 := jointlySmooth_foldr_deriv_action h1 l hl (Fin k → ℝ) id contDiff_id [] (by simp)
    simpa [List.map_ofFn, Function.comp_def] using h2

end GlobalTheory
