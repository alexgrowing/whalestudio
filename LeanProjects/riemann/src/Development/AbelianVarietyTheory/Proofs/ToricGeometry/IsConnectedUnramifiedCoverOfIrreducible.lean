import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.NodupRootsOfDerivativeNeZero

open Filter Topology

namespace GlobalTheory.SimpleRoots

open Polynomial

variable {d : ℕ}

open Classical in

noncomputable def partialProd (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : ℂ[X] :=
  (((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u).map fun y => X - C y).prod

theorem card_roots_map {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) (x : Fin d → ℂ) :
    (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := by
  rw [IsAlgClosed.card_roots_eq_natDegree, hp.natDegree_map]

theorem natDegree_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : (partialProd p u x).natDegree ≤ p.natDegree := by
  classical
  unfold partialProd
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← card_roots_map hp x]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem partialProd_mul_compl {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) :
    partialProd p u x * partialProd p uᶜ x = p.map (MvPolynomial.eval x) := by
  classical
  unfold partialProd
  rw [← Multiset.prod_add, ← Multiset.map_add]
  convert Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map (MvPolynomial.eval x))
    (by rw [card_roots_map hp x, hp.natDegree_map]) using 3
  convert Multiset.filter_add_not (fun y => (x, y) ∈ u) (p.map (MvPolynomial.eval x)).roots using 2
  congr 1

theorem exists_norm_coeff_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ (C : ℝ) (m : ℕ), ∀ k x, ‖(partialProd p u x).coeff k‖ ≤ C * (1 + ‖x‖) ^ m := by
  classical
  obtain ⟨C₀, m₀, hC₀, hroot⟩ := exists_norm_root_le hp
  refine ⟨(1 + C₀) ^ p.natDegree, m₀ * p.natDegree, fun k x => ?_⟩
  set R := C₀ * (1 + ‖x‖) ^ m₀ with hR
  have ht : 1 ≤ (1 + ‖x‖) ^ m₀ := one_le_pow₀ (by linarith [norm_nonneg x])
  have hR0 : 0 ≤ R := mul_nonneg hC₀ (by linarith)
  have hbound := norm_coeff_prod_le
    ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) hR0
    (fun y hy => hroot x y ((Polynomial.mem_roots (hp.map _).ne_zero).mp
      (Multiset.mem_of_mem_filter hy))) k
  have hcard : Multiset.card ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) ≤
      p.natDegree := by
    rw [← card_roots_map hp x]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have h1R : 1 + R ≤ (1 + C₀) * (1 + ‖x‖) ^ m₀ := by
    rw [hR]; nlinarith
  calc ‖(partialProd p u x).coeff k‖ ≤ (1 + R) ^ Multiset.card
          ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) := hbound
    _ ≤ (1 + R) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hcard
    _ ≤ ((1 + C₀) * (1 + ‖x‖) ^ m₀) ^ p.natDegree := pow_le_pow_left₀ (by linarith) h1R _
    _ = (1 + C₀) ^ p.natDegree * (1 + ‖x‖) ^ (m₀ * p.natDegree) := by rw [mul_pow, ← pow_mul]

theorem differentiableAt_coeff_partialProd {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {u : Set ((Fin d → ℂ) × ℂ)} {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0)
    (hu : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
      (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u)) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (partialProd p u x).coeff k) x₀ := by
  classical
  obtain ⟨ψ, hψ, hroots⟩ := exists_analytic_roots hp h
  set R₀ := (p.map (MvPolynomial.eval x₀)).roots with hR₀
  have hψc : ∀ y ∈ R₀, ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 →
      ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) := by
    intro y hy
    have hy0 : (p.map (MvPolynomial.eval x₀)).eval y = 0 :=
      (Polynomial.mem_roots (hp.map _).ne_zero).mp hy
    have ht : Tendsto (fun x => (x, ψ y x)) (𝓝 x₀) (𝓝 (x₀, y)) := by
      have := (continuousAt_id.prodMk (hψ y hy).1.continuousAt).tendsto
      simpa [(hψ y hy).2] using this
    exact ht.eventually (hu y hy0)
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ R₀.toFinset,
      (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 → ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) :=
    (Filter.eventually_all_finset _).mpr fun y hy => hψc y (Multiset.mem_toFinset.mp hy)
  have heq : (fun x => (partialProd p u x).coeff k) =ᶠ[𝓝 x₀]
      fun x => ((R₀.filter fun y => (x₀, y) ∈ u).map fun y => X - C (ψ y x)).prod.coeff k := by
    filter_upwards [hroots, hall] with x hx hxa
    unfold partialProd
    rw [hx, Multiset.filter_map, Multiset.map_map]
    congr 3
    refine Multiset.filter_congr fun y hy => ?_
    refine hxa y (Multiset.mem_toFinset.mpr hy) ?_
    have hmem : ψ y x ∈ (p.map (MvPolynomial.eval x)).roots := by
      rw [hx]; exact Multiset.mem_map_of_mem _ hy
    exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hmem
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact differentiableAt_coeff_prod _ ψ
    (fun y hy => (hψ y (Multiset.mem_of_mem_filter hy)).1.differentiableAt) k

theorem eq_of_map_eval_eq_of_dense {a b : Polynomial (MvPolynomial (Fin d) ℂ)}
    {U : Set (Fin d → ℂ)} (hU : Dense U)
    (h : ∀ x ∈ U, a.map (MvPolynomial.eval x) = b.map (MvPolynomial.eval x)) : a = b := by
  ext i
  have hfun : (fun x => MvPolynomial.eval x (a.coeff i)) = fun x => MvPolynomial.eval x (b.coeff i) := by
    refine Continuous.ext_on hU (MvPolynomial.continuous_eval _) (MvPolynomial.continuous_eval _) ?_
    intro x hx
    have := congrArg (fun P => Polynomial.coeff P i) (h x hx)
    simpa [Polynomial.coeff_map] using this
  exact congrArg (fun c => MvPolynomial.coeff _ c) (MvPolynomial.funext fun x => congrFun hfun x)

end GlobalTheory.SimpleRoots

namespace GlobalTheory

open SimpleRoots

theorem isConnected_unramified_cover_of_irreducible :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) →
    (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) →
    (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ),
      p.Monic → Irreducible p → q ≠ 0 →
      (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 →
        (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) →
      IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) := by
  intro H1 H2 d p q hp hirr hq hsimp
  obtain ⟨hΩc, hΩd⟩ := H1 d q hq
  have hΩo : IsOpen {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
  have hdeg : p.natDegree ≠ 0 := by
    intro h0
    exact hirr.not_isUnit (by rw [hp.natDegree_eq_zero.mp h0]; exact isUnit_one)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hΩc.nonempty
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by rw [card_roots_map hp x]; omega : 0 < Multiset.card (p.map (MvPolynomial.eval x)).roots)
    exact ⟨(x, y), hx, (Polynomial.mem_roots (hp.map _).ne_zero).mp hy⟩
  intro u v hu hv hZ hZu hZv
  by_contra hne
  have hdisj : ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
      (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ u → z ∉ v :=
    fun z hzq hz0 hzu hzv => hne ⟨z, ⟨hzq, hz0⟩, hzu, hzv⟩
  have hloc : ∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      ∀ᶠ w in 𝓝 (x₀, y), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u) := by
    intro x₀ hx₀ y hy
    by_cases hyu : (x₀, y) ∈ u
    · filter_upwards [hu.mem_nhds hyu] with w hw _ using iff_of_true hw hyu
    · have hyv : (x₀, y) ∈ v := (@hZ (x₀, y) ⟨hx₀, hy⟩).resolve_left hyu
      filter_upwards [hv.mem_nhds hyv,
        continuous_fst.continuousAt.preimage_mem_nhds (hΩo.mem_nhds hx₀)] with w hwv hwq hw0
      exact iff_of_false (fun hwu => hdisj w hwq hw0 hwu hwv) hyu
  have hpoly : ∀ s : Set ((Fin d → ℂ) × ℂ), (∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y,
      (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
        (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ s ↔ (x₀, y) ∈ s)) →
      ∃ A : Polynomial (MvPolynomial (Fin d) ℂ), ∀ x, MvPolynomial.eval x q ≠ 0 →
        A.map (MvPolynomial.eval x) = partialProd p s x := by
    intro s hs
    obtain ⟨C₁, m, hC₁⟩ := exists_norm_coeff_partialProd_le hp s
    have hk : ∀ k, ∃ a : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        (partialProd p s x).coeff k = MvPolynomial.eval x a := fun k =>
      H2 d m q (fun x => (partialProd p s x).coeff k) C₁ hq
        (fun x hx => (differentiableAt_coeff_partialProd hp (fun y hy => hsimp x y hx hy)
          (hs x hx) k).differentiableWithinAt)
        (fun x _ => hC₁ k x)
    choose a ha using hk
    refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k), fun x hx => ?_⟩
    ext k
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk'
    · exact (ha k x hx).symm
    · have := natDegree_partialProd_le hp s x
      rw [map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  obtain ⟨A, hA⟩ := hpoly u hloc
  obtain ⟨B, hB⟩ := hpoly uᶜ fun x₀ hx₀ y hy =>
    (hloc x₀ hx₀ y hy).mono fun w hw h0 => not_congr (hw h0)
  have hAB : A * B = p := eq_of_map_eval_eq_of_dense hΩd fun x hx => by
    rw [Polynomial.map_mul, hA x hx, hB x hx, partialProd_mul_compl hp]
  have hnot : ∀ (s : Set ((Fin d → ℂ) × ℂ)) (A' : Polynomial (MvPolynomial (Fin d) ℂ)),
      (∀ x, MvPolynomial.eval x q ≠ 0 → A'.map (MvPolynomial.eval x) = partialProd p s x) →
      ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ s → ¬ IsUnit A' := by
    intro s A' hA' z hzq hz0 hzs hunit
    classical
    have hu' : IsUnit (A'.map (MvPolynomial.eval z.1)) :=
      hunit.map (Polynomial.mapRingHom (MvPolynomial.eval z.1))
    rw [hA' z.1 hzq] at hu'
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit hu'
    unfold partialProd at h2
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_eq_zero] at h2
    exact Multiset.filter_eq_nil.mp h2 z.2 ((Polynomial.mem_roots (hp.map _).ne_zero).mpr hz0) hzs
  obtain ⟨z, ⟨hzq, hz0⟩, hzu⟩ := hZu
  obtain ⟨z', ⟨hzq', hz0'⟩, hzv'⟩ := hZv
  rcases hirr.isUnit_or_isUnit hAB.symm with h | h
  · exact hnot u A hA z hzq hz0 hzu h
  · exact hnot uᶜ B hB z' hzq' hz0' (fun hzu' => hdisj z' hzq' hz0' hzu' hzv') h

end GlobalTheory
