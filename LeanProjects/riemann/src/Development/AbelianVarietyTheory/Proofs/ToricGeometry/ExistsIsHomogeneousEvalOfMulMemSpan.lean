import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private theorem isWeightedHomogeneous_coeff_mul_rw1 {X ρ : Type} (b : ρ → X → ℂ) {k l : ℕ} {f g : X → ℂ}
    (hf : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G)
    (hg : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous l ∧
      ∀ z, g z = MvPolynomial.eval (fun c => b c z) G) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous (k + l) ∧
      ∀ z, f z * g z = MvPolynomial.eval (fun c => b c z) G := by
  obtain ⟨G, hG, hfG⟩ := hf
  obtain ⟨H, hH, hgH⟩ := hg
  exact ⟨G * H, hG.mul hH, fun z => by rw [hfG, hgH, map_mul]⟩

private theorem exists_homogeneous_one_eval_of_mem_span {X ρ : Type} (b : ρ → X → ℂ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range b)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous 1 ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (R := ℂ) i, fun z => by simp⟩
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, hxG⟩ := hx
    obtain ⟨H, hH, hyH⟩ := hy
    exact ⟨G + H, hG.add hH, fun z => by simp [hxG, hyH]⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, hxG⟩ := hx
    have hCG := (MvPolynomial.isHomogeneous_C (σ := ρ) c).mul hG
    rw [zero_add] at hCG
    exact ⟨MvPolynomial.C c * G, hCG, fun z => by simp [hxG]⟩

private theorem exists_homogeneous_eval_of_even_degree_monomial {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree = 2 * k →
      ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
        ∀ z, (m.prod fun c e => a c z ^ e) = MvPolynomial.eval (fun c => b c z) G := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [mul_zero, Finsupp.degree_eq_zero_iff] at hm
    subst hm
    exact ⟨1, MvPolynomial.isHomogeneous_one _ _, fun z => by simp⟩
  | succ k ih =>
    intro m hm
    classical
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₁ : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + Finsupp.single i 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₁).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    obtain ⟨j, hj⟩ : ∃ j, m₁ j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m₁ = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₂ : Finsupp.single j 1 ≤ m₁ := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + Finsupp.single j 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₂).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    have hdeg : m₂.degree = 2 * k := by omega
    obtain ⟨G, hG, hGz⟩ := isWeightedHomogeneous_coeff_mul_rw1 b (ih m₂ hdeg) (exists_homogeneous_one_eval_of_mem_span b (hab j i))
    refine ⟨G, hG, fun z => ?_⟩
    rw [← hGz z, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Pi.mul_apply]
    ring

theorem exists_isHomogeneous_eval_of_mul_mem_span {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) (d : ℕ) (F : MvPolynomial σ ℂ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, MvPolynomial.eval (fun c => a c z) F = MvPolynomial.eval (fun c => b c z) G := by
  classical
  have hP : ∀ s : Finset (σ →₀ ℕ), s ⊆ F.support → ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, (∑ m ∈ s, F.coeff m * m.prod fun c e => a c z ^ e) =
        MvPolynomial.eval (fun c => b c z) G := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
    | insert m s hms ih =>
      intro hsub
      obtain ⟨G, hG, hGz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hm : m.degree = 2 * d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF (MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self m s)))
      obtain ⟨H, hH, hHz⟩ := exists_homogeneous_eval_of_even_degree_monomial a b hab d m hm
      have hCH := (MvPolynomial.isHomogeneous_C (σ := ρ) (F.coeff m)).mul hH
      rw [zero_add] at hCH
      refine ⟨MvPolynomial.C (F.coeff m) * H + G, hCH.add hG, fun z => ?_⟩
      rw [Finset.sum_insert hms, hGz z, hHz z]
      simp
  obtain ⟨G, hG, hGz⟩ := hP F.support subset_rfl
  exact ⟨G, hG, fun z => by rw [MvPolynomial.eval_eq, ← hGz z]; rfl⟩

theorem theta_projectiveNormality_even :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ Even N ∧ (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F)) := by
  intro hA hB hC g τ hτ
  obtain ⟨N, hN3, hNC⟩ := hC g τ hτ
  refine ⟨2 * N, by omega, even_two_mul N, fun d f hf => ?_⟩
  obtain ⟨F, hF, hFz⟩ := hNC (2 * d) f
    ⟨hf.1, fun n n' z => by rw [show N * (2 * d) = 2 * N * d by ring]; exact hf.2 n n' z⟩
  have hA' := (hA g τ hτ N (by omega)).1
  have hab : ∀ i j : Fin g → Fin N,
      (fun z : Fin g → ℂ => theta (fun k => ((i k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) *
        (fun z : Fin g → ℂ => theta (fun k => ((j k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∈
      Submodule.span ℂ (Set.range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
        theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
          (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))) := by
    intro i j
    refine hB g τ hτ (2 * N) (by omega) _ ⟨(hA' i).1.mul (hA' j).1, fun n n' z => ?_⟩
    have h1 := (hA' i).2 n n' z
    have h2 := (hA' j).2 n n' z
    beta_reduce at h1 h2 ⊢
    rw [Pi.mul_apply, Pi.mul_apply, h1, h2,
      show ∀ x : ℂ, eC (-((2 * N : ℕ) : ℂ) * x) = eC (-(N : ℂ) * x) * eC (-(N : ℂ) * x) from
        fun x => by unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  obtain ⟨G, hG, hGz⟩ := exists_isHomogeneous_eval_of_mul_mem_span
    (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
    (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
        (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))
    hab d F hF
  exact ⟨G, hG, fun z => (hFz z).trans (hGz z)⟩

end GlobalTheory
