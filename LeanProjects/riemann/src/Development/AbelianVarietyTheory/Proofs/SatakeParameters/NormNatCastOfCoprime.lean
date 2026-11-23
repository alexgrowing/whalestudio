import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota

open NumberField

namespace GlobalTheory.CoprimeUnitMultipliers

theorem exists_common_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : R → Prop) (h1 : U 1) (hm : ∀ a b, U a → U b → U (a * b))
    (M N : Submodule R V) (hM : M.FG) (h : ∀ x ∈ M, ∃ s, U s ∧ s • x ∈ N) :
    ∃ s, U s ∧ ∀ x ∈ M, s • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have key : ∀ T : Finset V, (∀ x ∈ T, ∃ s, U s ∧ s • x ∈ N) → ∃ s, U s ∧ ∀ x ∈ T, s • x ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1, by simp⟩
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, hm _ _ hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [mul_smul]; exact N.smul_mem _ hta
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (hsT x hx)
  obtain ⟨s, hs, hS⟩ := key S fun x hx => h x (Submodule.subset_span hx)
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem norm_natCast_of_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) :
    ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

theorem general {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p]) {N N' : ℕ}
    (L L₁ : Submodule (𝓞 E) (Fin N → E)) (L' L₁' : Submodule (𝓞 E) (Fin N' → E))
    (P : Matrix (Fin N) (Fin N) E) (P' : Matrix (Fin N') (Fin N') E) (hfg : L₁.FG)
    (s : ℕ) (hs : Nat.Coprime s p) (hL : ∀ x ∈ L₁, (s : E) • x ∈ L)
    (s' : ℕ) (hs' : Nat.Coprime s' p) (hL' : ∀ x ∈ L', (s' : E) • x ∈ L₁')
    (hdet : P.det ≠ 0)
    (hP : ∀ x ∈ L, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, t • x = ∑ a, c a • P.transpose a)
    (hP' : ∀ a, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ t • P'.transpose a ∈ L') :
    ∃ σ σ' : 𝓞 E, ‖ρ (σ : E)‖ = 1 ∧ ‖ρ (σ' : E)‖ = 1 ∧
      (∀ a : Fin N, ∀ x ∈ L₁, ∃ o : 𝓞 E, (o : E) = (σ : E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧
      ∀ b : Fin N', (fun i : Fin N' => (σ' : E) * P' i b) ∈ L₁' := by
  have h1 : ‖ρ ((1 : 𝓞 E) : E)‖ = 1 := by simp
  have hm : ∀ a b : 𝓞 E, ‖ρ (a : E)‖ = 1 → ‖ρ (b : E)‖ = 1 → ‖ρ ((a * b : 𝓞 E) : E)‖ = 1 := by
    intro a b ha hb
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb ⊢
    rw [map_mul, map_mul, norm_mul, ha, hb, one_mul]
  have hn : ∀ n : ℕ, Nat.Coprime n p → ‖ρ (((n : 𝓞 E)) : E)‖ = 1 := by
    intro n hn
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_of_coprime hn
  have hsm : ∀ {k : ℕ} (n : ℕ) (x : Fin k → E), (n : 𝓞 E) • x = (n : E) • x := by
    intro k n x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨σ, hσ, hσL⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm L₁
    (Submodule.span (𝓞 E) (Set.range P.transpose)) hfg (by
      intro x hx
      obtain ⟨t, ht, c, hc⟩ := hP _ (hL x hx)
      refine ⟨t * s, hm _ _ ht (hn s hs), ?_⟩
      rw [mul_smul, hsm, hc]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨σ', hσ', hσL'⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm
    (Submodule.span (𝓞 E) (Set.range P'.transpose)) L₁'
    (Submodule.fg_span (Set.finite_range _)) (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨t, ht, hta⟩ := hP' a
        refine ⟨s' * t, hm _ _ (hn s' hs') ht, ?_⟩
        rw [mul_smul, hsm]
        exact hL' _ hta
      | zero => exact ⟨1, h1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, htx⟩ := hx
        obtain ⟨u, hu, huy⟩ := hy
        refine ⟨t * u, hm _ _ ht hu, ?_⟩
        rw [smul_add]
        refine L₁'.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L₁'.smul_mem _ htx
        · rw [mul_smul]; exact L₁'.smul_mem _ huy
      | smul a x _ hx =>
        obtain ⟨t, ht, htx⟩ := hx
        exact ⟨t, ht, by rw [smul_comm]; exact L₁'.smul_mem _ htx⟩)
  refine ⟨σ, σ', hσ, hσ', fun a x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hσL x hx)
    refine ⟨c a, ?_⟩
    have e1 : P.mulVec (fun i => (c i : E)) = (σ : E) • x := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [RingOfIntegers.coe_eq_algebraMap σ, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : (fun i => (c i : E)) = (σ : E) • P⁻¹.mulVec x := by
      rw [← Matrix.mulVec_smul, ← e1, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
    have := congrFun e2 a
    simpa [Matrix.mulVec, dotProduct] using this
  · have := hσL' _ (Submodule.subset_span ⟨b, rfl⟩)
    convert this using 1
    funext i
    simp only [Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def]

theorem exists_unit_multipliers : ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [inst : Fact (Nat.Prime p)] (ρ : (Formalism.BasicNotions.D7.host D).E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E)) (L' L₁' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)) (P : Matrix (Fin N) (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (P' : Matrix (Fin N') (Fin N') ((Formalism.BasicNotions.D7.host D).E)), Submodule.FG L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L P → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L' P' → ∃ (σ : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (σ' : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ' : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ (∀ (a : Fin N), ∀ x ∈ L₁, ∃ (o : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), (↑o : (Formalism.BasicNotions.D7.host D).E) = (↑σ : (Formalism.BasicNotions.D7.host D).E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧ ∀ (b : Fin N'), (fun (i : Fin N') ↦ (↑σ' : (Formalism.BasicNotions.D7.host D).E) * P' i b) ∈ L₁' := by
  intro D p inst ρ N N' L L₁ L' L₁' P P' hfg h h' hP hP'
  obtain ⟨s, hs, -, hL⟩ := h
  obtain ⟨s', hs', hL', -⟩ := h'
  exact general ρ L L₁ L' L₁' P P' hfg s hs hL s' hs' hL' hP.1 hP.2.2 hP'.2.1

end GlobalTheory.CoprimeUnitMultipliers
