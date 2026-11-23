import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothForms.SecondKind

open NormedSpace

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
private theorem isLieData_star_pow (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (x : 𝔸) (n : ℕ) :
    σ (x ^ n) = σ x ^ n := by
  induction n with
  | zero => simpa using H.one
  | succ n ih => rw [pow_succ, H.anti, ih, ← pow_succ']

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
private theorem isLieData_star_exp (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (x : 𝔸) :
    σ (exp x) = exp (σ x) := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  have h1 := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mapL (LinearMap.toContinuousLinearMap σ)
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) (σ x)
  have h3 : (fun n : ℕ => LinearMap.toContinuousLinearMap σ (((n.factorial : ℝ))⁻¹ • x ^ n)) =
      fun n => ((n.factorial : ℝ))⁻¹ • σ x ^ n := by
    funext n
    simp [isLieData_star_pow H]
  rw [h3] at h1
  exact h1.unique h2

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
theorem _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (X : L) :
    σ (exp (j X)) * exp (j X) = 1 := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  have hX : σ (j X) = -(j X) := (H.skew _).2 ⟨X, rfl⟩
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [isLieData_star_exp H, hX, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)),
    neg_add_cancel, exp_zero]

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
omit [FiniteDimensional ℝ 𝔸] in
theorem _root_.GlobalTheory.SmoothForms.SecondKind.map_one_eq (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) : s 1 = 1 := by
  have h := H.mul 1 1 (by rw [H.one, one_mul])
    (by rw [H.one, one_mul])
  rw [one_mul] at h
  exact mul_left_cancel (a := s 1) (by rw [mul_one]; exact h.symm)

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
theorem _root_.GlobalTheory.SmoothForms.SecondKind.contDiff_exp : ContDiff ℝ ∞ (exp : 𝔸 → 𝔸) := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  exact AnalyticOnNhd.contDiff fun x _ => exp_analytic x

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem prod_exp (H : IsLieData σ j s) (J : L →L[ℝ] 𝔸) (hJ : ∀ X, J X = j X) (l : List (P →L[ℝ] L)) :
    ∃ c : P → 𝔸, ContDiff ℝ ∞ c ∧ (∀ p, σ (c p) * c p = 1) ∧
      (∀ p, s (c p) = (l.map fun A => expMap j s (A p)).prod) ∧ c 0 = 1 ∧ HasFDerivAt c (J ∘L l.sum) 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  induction l with
  | nil =>
    refine ⟨fun _ => 1, contDiff_const, fun _ => by simp [H.one], fun _ => by simp [map_one_eq H], rfl, ?_⟩
    simpa using hasFDerivAt_const (1 : 𝔸) (0 : P)
  | cons A l ih =>
    obtain ⟨c, h1, h2, h3, h4, h5⟩ := ih
    have hA : ContDiff ℝ ∞ fun p => exp (J (A p)) := contDiff_exp.comp (J ∘L A).contDiff
    have hu : ∀ p, σ (exp (J (A p))) * exp (J (A p)) = 1 := fun p => by rw [hJ]; exact exp_unitary H _
    refine ⟨fun p => exp (J (A p)) * c p, hA.mul h1, fun p => ?_, fun p => ?_, by simp [h4], ?_⟩
    · rw [H.anti, mul_assoc, ← mul_assoc (σ (exp _)), hu, one_mul, h2]
    · rw [H.mul _ _ (hu p) (h2 p), h3, hJ, List.map_cons, List.prod_cons, expMap]
    · have hd : HasFDerivAt (fun p => exp (J (A p))) (J ∘L A) 0 := by
        have := HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : P)
          (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) (J ∘L A).hasFDerivAt
        exact this
      refine (hd.mul' h5).congr_fderiv ?_
      ext p
      simp [h4, add_comm]

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_list_prod_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) :
    ∀ l : List 𝔸, (∀ a ∈ l, σ a * a = 1) → σ l.prod * l.prod = 1
  | [], _ => by simp [H.one]
  | a :: l, h => by
    rw [List.prod_cons, H.anti, mul_assoc, ← mul_assoc (σ a),
      h a (by simp), one_mul]
    exact isLieData_list_prod_unitary H l fun b hb => h b (by simp [hb])

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_s_list_prod_eq_prod_map_of_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) :
    ∀ l : List 𝔸, (∀ a ∈ l, σ a * a = 1) → s l.prod = (l.map s).prod
  | [], _ => by simpa using _root_.GlobalTheory.SmoothForms.SecondKind.map_one_eq H
  | a :: l, h => by
    rw [List.prod_cons, H.mul a l.prod (h a (by simp))
      (isLieData_list_prod_unitary H l fun b hb => h b (by simp [hb])), List.map_cons, List.prod_cons,
      isLieData_s_list_prod_eq_prod_map_of_unitary H l fun b hb => h b (by simp [hb])]

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_s_prod_exp_eq_prod_expMap (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) {k : ℕ} (Y : Fin k → L)
    (t : Fin k → ℝ) :
    s (List.ofFn fun i => exp (j (t i • Y i))).prod =
      (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod := by
  rw [isLieData_s_list_prod_eq_prod_map_of_unitary H _ ?_, List.map_ofFn]
  · rfl
  · intro a ha
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 ha
    exact _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H _

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem contDiff_list_prod_ofFn' :
    ∀ (k : ℕ) (F : Fin k → P → 𝔸), (∀ i, ContDiff ℝ ∞ (F i)) →
      ContDiff ℝ ∞ fun p => (List.ofFn fun i => F i p).prod
  | 0, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact contDiff_const
  | k + 1, F, hF => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hF 0).mul (contDiff_list_prod_ofFn' k (fun i => F i.succ) fun i => hF _)

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem contDiff_list_prod_ofFn_exp_smul {k : ℕ} (Y : Fin k → L) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => exp (j (t i • Y i))).prod := by
  refine contDiff_list_prod_ofFn' k _ fun i => ?_
  have h : (fun t : Fin k → ℝ => exp (j (t i • Y i))) = fun t => exp (t i • j (Y i)) := by
    funext t
    rw [map_smul]
  rw [h]
  exact _root_.GlobalTheory.SmoothForms.SecondKind.contDiff_exp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem isLieData_prod_exp_smul_unitary (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) {k : ℕ} (Y : Fin k → L)
    (t : Fin k → ℝ) :
    σ (List.ofFn fun i => exp (j (t i • Y i))).prod * (List.ofFn fun i => exp (j (t i • Y i))).prod
      = 1 := by
  refine isLieData_list_prod_unitary H _ fun a ha => ?_
  obtain ⟨m, rfl⟩ := List.mem_ofFn.1 ha
  exact _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H _

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem list_prod_ofFn_eq_of_eq_one_of_ne :
    ∀ (k : ℕ) (f : Fin k → 𝔸) (i : Fin k), (∀ m, m ≠ i → f m = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | k + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero m)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact list_prod_ofFn_eq_of_eq_one_of_ne k _ i fun m hm => h _ fun e => hm (Fin.succ_injective _ e)

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem _root_.GlobalTheory.SmoothForms.SecondKind.sm_iff (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) (T : Set L) (hT : Submodule.span ℝ T = ⊤) (φ : G → ℂ) :
    _root_.GlobalTheory.SmoothForms.Sm (_root_.GlobalTheory.SmoothForms.expMap j s) φ ↔
      ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod) := by
  have hfun : ∀ (g : G) {k : ℕ} (Y : Fin k → L),
      (fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod))
        = fun t => φ (g * s (List.ofFn fun i => exp (j (t i • Y i))).prod) := by
    intro g k Y
    funext t
    rw [isLieData_s_prod_exp_eq_prod_expMap H]
  constructor
  · intro hφ k Y _ g
    unfold _root_.GlobalTheory.SmoothForms.Sm at hφ
    rw [hfun]
    exact _root_.GlobalTheory.SmoothForms.contDiff_family H hl (fun g => (hφ g).contDiffAt)
      (contDiff_list_prod_ofFn_exp_smul Y) (isLieData_prod_exp_smul_unitary H Y) g
  · intro h
    obtain ⟨-, -, -, hinj, -, -⟩ := id H
    haveI : FiniteDimensional ℝ L := Module.Finite.of_injective j hinj
    haveI := FiniteDimensional.complete ℝ L
    haveI := FiniteDimensional.complete ℝ 𝔸
    have hj : ContDiff ℝ ∞ (j : L → 𝔸) := (LinearMap.toContinuousLinearMap j).contDiff
    obtain ⟨Λ, hΛ, hexpΛ, hΛexp⟩ := id hl

    obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℝ T
    haveI : Fintype b := hbli.setFinite.fintype
    let B : Module.Basis b ℝ L := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hT])
    let Y : Fin (Fintype.card b) → L := B.reindex (Fintype.equivFin b)
    have hYT : ∀ i, Y i ∈ T := fun i => by
      simp only [Y, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
      exact hbT (Subtype.mem _)
    let Φ : (Fin (Fintype.card b) → ℝ) → 𝔸 := fun t => (List.ofFn fun i => exp (j (t i • Y i))).prod
    have hΦ : ContDiff ℝ ∞ Φ := contDiff_list_prod_ofFn_exp_smul Y
    have hΦ0 : Φ 0 = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
      simp
    let Ψ : (Fin (Fintype.card b) → ℝ) → L := fun t => Λ (Φ t)
    have hΨ : ContDiffAt ℝ ∞ Ψ 0 := by
      have : ContDiffAt ℝ ∞ Λ (Φ 0) := by rw [hΦ0]; exact hΛ
      exact this.comp 0 hΦ.contDiffAt
    have hΨ0 : Ψ 0 = 0 := by
      have := hΛexp.self_of_nhds
      rw [map_zero, exp_zero] at this
      show Λ (Φ 0) = 0
      rw [hΦ0, this]

    have hsingle : ∀ (i : Fin (Fintype.card b)) (x : ℝ), fderiv ℝ Ψ 0 (Pi.single i x) = x • Y i := by
      intro i x
      have hd := (hΨ.differentiableAt (by simp)).hasFDerivAt
      have h1 := hd.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i x))
        (by simp)
      have h2 := (hasDerivAt_id (0 : ℝ)).smul_const (x • Y i)
      have hev : (fun r : ℝ => r • (x • Y i)) =ᶠ[𝓝 0] Ψ ∘ fun r => id r • Pi.single i x := by
        have ht : Filter.Tendsto (fun r : ℝ => (r * x) • Y i) (𝓝 0) (𝓝 0) := by
          have : Continuous fun r : ℝ => (r * x) • Y i := by fun_prop
          simpa using this.tendsto 0
        filter_upwards [ht.eventually hΛexp] with r hr
        have hprod : Φ (id r • Pi.single i x) = exp (j ((r * x) • Y i)) := by
          simp only [Φ]
          rw [list_prod_ofFn_eq_of_eq_one_of_ne _ _ i]
          · simp
          · intro m hm
            simp [Pi.single_apply, hm]
        show r • (x • Y i) = Λ (Φ (id r • Pi.single i x))
        rw [hprod, hr, mul_smul]
      have := h1.unique (h2.congr_of_eventuallyEq hev.symm)
      simpa using this
    let e : (Fin (Fintype.card b) → ℝ) ≃L[ℝ] L :=
      (B.reindex (Fintype.equivFin b)).equivFun.symm.toContinuousLinearEquiv
    have he : ∀ (i : Fin (Fintype.card b)) (x : ℝ), e (Pi.single i x) = x • Y i := by
      intro i x
      simp [e, Y, Module.Basis.equivFun_symm_apply, Pi.single_apply]
    have hd : HasFDerivAt Ψ (e : (Fin (Fintype.card b) → ℝ) →L[ℝ] L) 0 := by
      have hd := (hΨ.differentiableAt (by simp)).hasFDerivAt
      have heq : (e : (Fin (Fintype.card b) → ℝ) →L[ℝ] L) = fderiv ℝ Ψ 0 := by
        ext1 v
        rw [← Finset.univ_sum_single v, map_sum, map_sum]
        simp only [ContinuousLinearEquiv.coe_coe, he, hsingle]
      rw [heq]
      exact hd
    have hs := hΨ.hasStrictFDerivAt' hd (by simp)
    let Ψinv := hs.localInverse Ψ e 0
    have hinv0 : Ψinv 0 = 0 := by
      have := hs.localInverse_apply_image
      rwa [hΨ0] at this
    have hinv : ContDiffAt ℝ ∞ Ψinv 0 := by
      have := hΨ.to_localInverse hd (by simp)
      rw [hΨ0] at this
      exact this
    have hright : ∀ᶠ X in 𝓝 (0 : L), Ψ (Ψinv X) = X := by
      have := hs.eventually_right_inverse
      rwa [hΨ0] at this
    have hnear : ∀ᶠ X in 𝓝 (0 : L),
        σ (Φ (Ψinv X)) * Φ (Ψinv X) = 1 → exp (j (Λ (Φ (Ψinv X)))) = Φ (Ψinv X) := by
      have hc : ContinuousAt Ψinv 0 := by
        have := hs.localInverse_continuousAt
        rwa [hΨ0] at this
      have ht : Filter.Tendsto (fun X => Φ (Ψinv X)) (𝓝 0) (𝓝 1) := by
        have := hΦ.continuous.continuousAt.comp hc
        rw [ContinuousAt, Function.comp_apply, hinv0, hΦ0] at this
        exact this
      exact ht.eventually hexpΛ
    unfold _root_.GlobalTheory.SmoothForms.Sm
    have h0 : ∀ g, ContDiffAt ℝ ∞ (fun X => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0 := by
      intro g
      have hF : ContDiff ℝ ∞ fun t => φ (g * s (Φ t)) := by
        have := h _ Y hYT g
        rw [hfun] at this
        exact this
      have hcomp : ContDiffAt ℝ ∞ (fun X => φ (g * s (Φ (Ψinv X)))) 0 := by
        have h2 : ContDiffAt ℝ ∞ (fun t => φ (g * s (Φ t))) (Ψinv 0) := hF.contDiffAt
        exact h2.comp 0 hinv
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [hright, hnear] with X hX1 hX2
      have := hX2 (isLieData_prod_exp_smul_unitary H Y _)
      change Λ (Φ (Ψinv X)) = X at hX1
      rw [hX1] at this
      show φ (g * s (exp (j X))) = φ (g * s (Φ (Ψinv X)))
      rw [this]
    intro g
    exact _root_.GlobalTheory.SmoothForms.contDiff_family H hl h0
      (_root_.GlobalTheory.SmoothForms.SecondKind.contDiff_exp.comp hj) (fun X => _root_.GlobalTheory.SmoothForms.SecondKind.exp_unitary H X) g

open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem _root_.GlobalTheory.SmoothForms.SecondKind.main : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
    [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), _root_.GlobalTheory.SmoothForms.IsLieData σ j s →
    _root_.GlobalTheory.SmoothForms.HasLog σ j →
    ∀ T : Set L, Submodule.span ℝ T = ⊤ → ∀ φ : G → ℂ, _root_.GlobalTheory.SmoothForms.Sm (_root_.GlobalTheory.SmoothForms.expMap j s) φ ↔
      ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod) := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl T hT φ
  exact _root_.GlobalTheory.SmoothForms.SecondKind.sm_iff H hl T hT φ

end GlobalTheory.SmoothForms.SecondKind

end
