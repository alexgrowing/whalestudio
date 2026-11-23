import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.SliceLdiv

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem frobSlice_zero (l i : ℕ) : frobSlice l i (0 : K⟦X⟧) = 0 := by
  ext n; simp [coeff_frobSlice]

theorem frobSlice_sum {β : Type} (l i : ℕ) (s : Finset β) (g : β → K⟦X⟧) :
    frobSlice l i (∑ b ∈ s, g b) = ∑ b ∈ s, frobSlice l i (g b) := by
  ext n; simp [coeff_frobSlice, map_sum]

theorem frobSlice_mul_frob {l : ℕ} [Fact l.Prime] {i : ℕ} (hi : i < l) (z f : K⟦X⟧) :
    frobSlice l i (z * frob K l f) = frobSlice l i z * f := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  have hval : ∀ p q : ℕ, coeff (l * p + i) z * coeff q f =
      coeff (l * p + i) z * coeff (l * q) (frob K l f) := by
    intro p q
    rw [coeff_frob, if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q hl]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1 + i, l * p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq -
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hpq ⊢
    rw [← hpq, mul_add]; ring
  · rintro ⟨p, q⟩ - - ⟨p', q'⟩ - - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : p = p' := Nat.eq_of_mul_eq_mul_left hl (by omega)
    have h2' : q = q' := Nat.eq_of_mul_eq_mul_left hl h2
    rw [h1', h2']
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [coeff_frob] at hne
    split_ifs at hne with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have hq : q ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * q := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      have key : l * (n - q) + l * q = l * n := by rw [← mul_add, Nat.sub_add_cancel hq]
      have ha : a = l * (n - q) + i := by omega
      subst ha
      rw [Nat.mul_div_cancel_left q hl] at hne
      exact ⟨(n - q, q), by simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega,
        by simp only [coeff_frobSlice]; exact hne, rfl⟩
    · exact absurd (mul_zero _) hne
  · rintro ⟨p, q⟩ - -
    simp only [coeff_frobSlice]
    exact hval p q

theorem bdd_frobSlice (l i : ℕ) {z : K⟦X⟧} (hz : ∃ c : ℝ, ∀ n, ‖coeff n z‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frobSlice l i z)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem bdd_zero : ∃ c : ℝ, ∀ n, ‖coeff n (0 : K⟦X⟧)‖ ≤ c := ⟨0, fun n => by simp⟩

theorem bdd_sum {β : Type} (s : Finset β) (g : β → K⟦X⟧) (hg : ∀ b ∈ s, ∃ c : ℝ, ∀ n, ‖coeff n (g b)‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (∑ b ∈ s, g b)‖ ≤ c :=
  Finset.sum_induction g (fun f : K⟦X⟧ => ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c)
    (fun _ _ => Hom.bdd_add) bdd_zero hg

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {M : Matrix μ ν K⟦X⟧} {N : Matrix ν ρ K⟦X⟧}
    (hM : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) (hN : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (N i j)‖ ≤ c)
    (i : μ) (j : ρ) : ∃ c : ℝ, ∀ n, ‖coeff n ((M * N) i j)‖ ≤ c := by
  rw [Matrix.mul_apply]
  exact bdd_sum _ _ fun k _ => Hom.bdd_mul (hM i k) (hN k j)

theorem bdd_unif {μ ν : Type} [Finite μ] [Finite ν] {M : Matrix μ ν K⟦X⟧}
    (h : ∀ i j, ∃ c : ℝ, ∀ n, ‖coeff n (M i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n (M i j)‖ ≤ c := by
  choose c hc using h
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : μ × ν => c p.1 p.2)
  exact ⟨C, fun i j n => (hc i j n).trans (hC ⟨(i, j), rfl⟩)⟩

theorem exists_pow_E_mul_mem (l e : ℕ) {β : Type} [Finite β] (g : β → K⟦X⟧)
    (hg : ∀ b, g b ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ b, E K l e ^ N * g b ∈ A O K := by
  have := Fintype.ofFinite β
  choose n hn using fun b => (mem_away.1 (hg b))
  refine ⟨Finset.univ.sup n, fun b => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ b))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn b)

theorem frobSlice_mem_ldivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.ldivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × ι × ι => P.mxInv p.1 p.2.1 p.2.2) (fun p => P.mxInv_mem _ _ _)
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mx p.1 p.2.1 p.2.2) (fun p => Q.mx_mem _ _ _)
  refine ⟨N₁ + N₂, fun τ h hh i hi => ?_⟩
  obtain ⟨hhb, Y, ⟨cY, hcY⟩, hY⟩ := hh
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix ι κ K⟦X⟧,
      Z = (E K l e ^ N₁ • P.mxInv τ) * Y * (E K l e ^ N₂ • Q.mx τ) := ⟨_, rfl⟩
  have h1 : Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l) = h • P.mx τ := by
    rw [Matrix.mul_assoc, ← F.comm, ← Matrix.mul_assoc, hY, Matrix.smul_mul, Matrix.one_mul]
  have hZF : Z * (F.mat (τ - 1)).map (frob K l) =
      (E K l e ^ (N₁ + N₂) * h) • (1 : Matrix ι ι K⟦X⟧) := by
    have : Z * (F.mat (τ - 1)).map (frob K l) =
        E K l e ^ N₁ • E K l e ^ N₂ • (P.mxInv τ * (Y * Q.mx τ * (F.mat (τ - 1)).map (frob K l))) := by
      simp only [hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      exact smul_comm _ _ _
    rw [this, h1, Matrix.mul_smul, P.mxInv_mul_mx]
    simp only [smul_smul, pow_add, mul_assoc]
  have hPb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₁ • P.mxInv τ) r k)‖ ≤ c := fun r k =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, r, k))
  have hQb : ∀ k c, ∃ c' : ℝ, ∀ n, ‖coeff n ((E K l e ^ N₂ • Q.mx τ) k c)‖ ≤ c' := fun k c =>
    bdd_of_mem_A (O := O) (by rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, k, c))
  have hYb : ∀ r k, ∃ c : ℝ, ∀ n, ‖coeff n (Y r k)‖ ≤ c := fun r k => ⟨cY, hcY r k⟩
  have hZb : ∀ r c, ∃ c' : ℝ, ∀ n, ‖coeff n (Z r c)‖ ≤ c' := fun r c => by
    rw [hZ]; exact bdd_matMul (bdd_matMul hPb hYb) hQb r c
  refine ⟨bdd_frobSlice l i (Hom.bdd_mul (bdd_of_mem_A (O := O) (pow_mem (E_mem l e (A O K)) _)) hhb),
    Z.map (frobSlice l i), bdd_unif fun r c => ?_, ?_⟩
  · rw [Matrix.map_apply]; exact bdd_frobSlice l i (hZb r c)
  · ext r c
    have hrc := congrFun (congrFun hZF r) c
    rw [Matrix.mul_apply] at hrc
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply] at hrc ⊢
    simp_rw [← frobSlice_mul_frob hi]
    rw [← frobSlice_sum, hrc, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_one]
    · rw [mul_zero, mul_zero, frobSlice_zero]

end GlobalTheory.BK.SliceLdiv
