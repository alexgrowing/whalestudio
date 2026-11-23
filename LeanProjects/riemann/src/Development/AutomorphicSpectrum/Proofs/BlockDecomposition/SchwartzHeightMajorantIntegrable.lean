import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ShearGrowth

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply block_diagonal_mul mat_mul')
open GlobalTheory.CompanionTheory.FourierN (mat_injective)

def rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : ℝ :=
  1 + ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2

theorem one_le_rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : 1 ≤ rr z := by
  unfold rr
  have : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem norm_le_rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : ‖z‖ ≤ rr z := by
  have h0 : (0 : ℝ) ≤ rr z := zero_le_one.trans (one_le_rr z)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i =>
    (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have h1 : ‖z τ i j‖ ^ 2 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 := by
    have hj : ‖z τ i j‖ ^ 2 ≤ ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    have hi : ∑ j, ‖z τ i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖z τ i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    have ht : ∑ i, ∑ j, ‖z τ i j‖ ^ 2 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖z τ i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  unfold rr
  nlinarith [sq_nonneg (‖z τ i j‖ - 1)]

theorem rr_temperate {ι : Type} [Fintype ι] {a b : ℕ} (L : ℕ) :
    (fun z : ι → Fin a → Fin b → ℂ => ((rr z : ℝ) : ℂ) ^ L).HasTemperateGrowth := by
  have hc : ∀ (τ : ι) (i : Fin a) (j : Fin b),
      (fun z : ι → Fin a → Fin b → ℂ => ‖z τ i j‖ ^ 2).HasTemperateGrowth := fun τ i j => by
    let P : (ι → Fin a → Fin b → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin b → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin a → Fin b → ℂ) τ))
    exact (Function.hasTemperateGrowth_norm_sq ℂ).comp P.hasTemperateGrowth
  have hr : (fun z : ι → Fin a → Fin b → ℂ => rr z).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).add
      (Function.HasTemperateGrowth.sum fun τ _ => Function.HasTemperateGrowth.sum fun i _ =>
        Function.HasTemperateGrowth.sum fun j _ => hc τ i j)
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp hr).pow L

theorem pow_bound {Γ : Type} [Group Γ] (h : Γ → ℝ) (e : ℝ → Γ) (he : ∀ u v, e (u + v) = e u * e v)
    (κ : ℝ) (hκ : 1 ≤ κ) (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ x, h (x * e u) ≤ κ * h x) (hpos : ∀ x, 0 ≤ h x) :
    ∀ (k : ℕ) (u : ℝ), |u| ≤ k → ∀ x, h (x * e u) ≤ κ ^ k * h x := by
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  intro k
  induction k with
  | zero =>
    intro u hu x
    have : u = 0 := by simpa using hu
    simp [this, he0]
  | succ k ih =>
    intro u hu x
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hu' : |u| ≤ (k : ℝ) + 1 := by simpa using hu
    have hw : u / (k + 1) ∈ Set.Icc (-1 : ℝ) 1 := by
      have : |u / ((k : ℝ) + 1)| ≤ 1 := by
        rw [abs_div, abs_of_pos hk, div_le_one hk]; exact hu'
      exact abs_le.1 this
    have hv : |u - u / (k + 1)| ≤ k := by
      have : u - u / ((k : ℝ) + 1) = u / ((k : ℝ) + 1) * k := by field_simp; ring
      rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have h1 : |u / ((k : ℝ) + 1)| ≤ 1 := abs_le.2 hw
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have e1 : u = u / (k + 1) + (u - u / (k + 1)) := by ring
    calc h (x * e u) = h (x * e (u / (k + 1)) * e (u - u / (k + 1))) := by
          rw [mul_assoc, ← he, ← e1]
      _ ≤ κ ^ k * h (x * e (u / (k + 1))) := ih _ hv _
      _ ≤ κ ^ k * (κ * h x) := by gcongr; exact hb _ hw x
      _ = κ ^ (k + 1) * h x := by ring

theorem exists_compact_fin (D : D7) (θ : InfFam D) (ρ p : ℕ) (Φ : Mx D ρ p → ℂ) (hΦ : Φ ∈ schwartzA θ ρ p) :
    ∃ S : Set (Fin ρ → Fin p → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact S ∧
      ∀ y, Φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ S := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨tsupport g, hg.2, fun y hy => subset_tsupport _ ?_⟩
    exact fun h0 => hy (by simp only [h0, mul_zero])
  | zero => exact ⟨∅, isCompact_empty, fun y hy => absurd rfl hy⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨S₁, c₁, s₁⟩ := h1
    obtain ⟨S₂, c₂, s₂⟩ := h2
    refine ⟨S₁ ∪ S₂, c₁.union c₂, fun y hy => ?_⟩
    by_cases h : Φ y = 0
    · exact Or.inr (s₂ y fun h' => hy (by simp [h, h']))
    · exact Or.inl (s₁ y h)
  | smul c Φ _ h =>
    obtain ⟨S, cS, sS⟩ := h
    exact ⟨S, cS, fun y hy => sS y fun h' => hy (by simp [h'])⟩

section Dil

variable {R : Type} [CommRing R] {n ρ p : ℕ}

theorem blockMatrix_smul_one_mul (hn : ρ + p = n) (α β : R) :
    HMul.hMul (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) =
      bl hn ((α * β) • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1 := by
  rw [blockMatrix_multiply]
  congr 1
  · simp [smul_smul, mul_comm]
  · simp
  · simp
  · simp

theorem blockMatrix_conj_upperUnipotent (hn : ρ + p = n) (α β : R) (h : α * β = 1) (y : Matrix (Fin ρ) (Fin p) R) :
    HMul.hMul (HMul.hMul (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn 1 y 0 1))
        (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) = bl hn 1 (α • y) 0 1 := by
  rw [blockMatrix_multiply, blockMatrix_multiply]
  congr 1
  · simp [smul_smul, mul_comm β α, h]
  · simp
  · simp
  · simp

theorem blockMatrix_conj_lowerUnipotent (hn : ρ + p = n) (α β : R) (h : α * β = 1) (c : Matrix (Fin p) (Fin ρ) R) :
    HMul.hMul (HMul.hMul (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn 1 0 c 1))
        (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) = bl hn 1 0 (α • c) 1 := by
  rw [blockMatrix_multiply, blockMatrix_multiply]
  congr 1
  · simp [smul_smul, h, mul_comm β α]
  · simp
  · simp
  · simp

end Dil

theorem exists_real_idele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ a : ℝ → AE D, Continuous a ∧ (∀ u v, a u * a v = a (u + v)) ∧ a 0 = 1 ∧
      (∀ u τ, θ τ (infPart D (a u)) = (Real.exp u : ℂ)) ∧ ∀ u, finPart D (a u) = 1 := by
  obtain ⟨e1, he1⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ 1 1
  have hinj : ∀ x x' : AE D, (∀ τ, θ τ (infPart D x) = θ τ (infPart D x')) → finPart D x = finPart D x' → x = x' := by
    intro x x' h1 h2
    have : (Matrix.of fun _ _ => x : Mx D 1 1) = Matrix.of fun _ _ => x' := by
      apply e1.injective
      rw [he1, he1]
      refine Prod.ext ?_ ?_
      · funext τ i j; exact h1 τ
      · funext i j; exact h2
    exact congrFun (congrFun this 0) 0
  let pt : ℝ → (D.what₂.Tau → Fin 1 → Fin 1 → ℂ) × (Fin 1 → Fin 1 → GlobalTheory.RegSch.IkSchwartz.AEf D) :=
    fun u => (fun _ _ _ => (Real.exp u : ℂ), fun _ _ => 1)
  have hpt : Continuous pt := by
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ =>
      Complex.continuous_ofReal.comp Real.continuous_exp
  let a : ℝ → AE D := fun u => e1.symm (pt u) 0 0
  have ha1 : ∀ u τ, θ τ (infPart D (a u)) = (Real.exp u : ℂ) := fun u τ => by
    have := congrArg Prod.fst (he1 (e1.symm (pt u)))
    rw [e1.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) 0) 0).symm
  have ha2 : ∀ u, finPart D (a u) = 1 := fun u => by
    have := congrArg Prod.snd (he1 (e1.symm (pt u)))
    rw [e1.apply_symm_apply] at this
    exact (congrFun (congrFun this 0) 0).symm
  refine ⟨a, (e1.symm.continuous.comp hpt).matrix_elem 0 0, fun u v => hinj _ _ (fun τ => ?_) ?_, hinj _ _ (fun τ => ?_) ?_, ha1, ha2⟩
  · rw [map_mul, map_mul, ha1, ha1, ha1, Real.exp_add, Complex.ofReal_mul]
  · rw [map_mul, ha2, ha2, ha2, one_mul]
  · rw [ha1, map_one, map_one]; simp
  · rw [ha2, map_one]

set_option maxHeartbeats 1000000 in

theorem dil_exists : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ℝ → G D n, Continuous e ∧ (∀ u v, e (u + v) = e u * e v) ∧
      ∀ (u : ℝ) (y y' : Mx D ρ p), (∀ τ i j, compAt θ τ y' i j = (Real.exp u : ℂ) * compAt θ τ y i j) →
        (∀ i j, finPart D (y' i j) = finPart D (y i j)) → M.sh y' = e u * M.sh y * e (-u) := by
  intro D θ hθ n ρ p hn M
  obtain ⟨a, hac, hmul, ha0, ha1, ha2⟩ := exists_real_idele D θ hθ
  obtain ⟨e0, he0⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ ρ p
  let A : ℝ → Mx D n n := fun u => bl hn (a u • (1 : Mx D ρ ρ)) 0 0 1
  have hA : ∀ u v, A u * A v = A (u + v) := fun u v => by
    show HMul.hMul _ _ = _
    rw [blockMatrix_smul_one_mul, hmul]
  have hA0 : A 0 = 1 := by
    show bl hn (a 0 • (1 : Mx D ρ ρ)) 0 0 1 = 1
    rw [ha0, one_smul]; exact GlobalTheory.CompanionTheory.PcB.blockMatrix_one hn
  have hAc : Continuous A := by
    have h1 : Continuous fun u => a u • (1 : Mx D ρ ρ) := by
      haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
      exact continuous_matrix fun i j => (hac.mul continuous_const : Continuous fun u => a u * (1 : Mx D ρ ρ) i j)
    exact (h1.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_submatrix _ _
  have hex : ∀ u, ∃ g : G D n, mat g = blk4 (A u) 0 0 (adj (A (-u))) := fun u =>
    GlobalTheory.StdUnn.Model.exists_levi ⟨A u, A (-u), by rw [hA, add_neg_cancel, hA0], by rw [hA, neg_add_cancel, hA0]⟩
  choose e he using hex
  have hadd : ∀ u v, e (u + v) = e u * e v := fun u v => by
    apply mat_injective
    rw [mat_mul', he, he, he, block_diagonal_mul]
    congr 1
    · exact (hA u v).symm
    · show _ = adj (A (-u)) * adj (A (-v))
      rw [← adj_mul, hA, neg_add_rev, add_comm (-v)]
  have he0' : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hinv : ∀ u, (e u)⁻¹ = e (-u) := fun u => by
    rw [inv_eq_iff_mul_eq_one, ← hadd, add_neg_cancel, he0']
  have hmc : Continuous fun u => mat (e u) := by
    simp only [he]
    exact ((hAc.matrix_fromBlocks continuous_const continuous_const
      (GlobalTheory.CompanionTheory.JacobiMaps.continuous_adjR.comp (hAc.comp continuous_neg))).matrix_submatrix _ _)
  refine ⟨e, GlobalTheory.StdUnn.continuous_of_mat_pt hmc ?_, hadd, fun u y y' h1 h2 => ?_⟩
  · simp only [hinv]
    exact hmc.comp continuous_neg
  have hy : y' = a u • y := by
    apply e0.injective
    rw [he0, he0]
    refine Prod.ext ?_ ?_
    · funext τ i j
      show compAt θ τ y' i j = θ τ (infPart D (a u * y i j))
      rw [h1, map_mul, map_mul, ha1]; rfl
    · funext i j
      show finPart D (y' i j) = finPart D (a u * y i j)
      rw [h2, map_mul, ha2, one_mul]
  apply mat_injective
  rw [mat_mul', mat_mul', he, he, M.sh_mat, M.sh_mat, block_diagonal_mul, block_diagonal_mul]
  have hau : a u * a (-u) = 1 := by rw [hmul, add_neg_cancel, ha0]
  have hcu : cA D (a u) * cA D (a (-u)) = 1 := by rw [← map_mul, hau, map_one]
  have hadjA : ∀ v, adj (A v) = bl hn (cA D (a v) • (1 : Mx D ρ ρ)) 0 0 1 := fun v => by
    show adj (bl hn (a v • (1 : Mx D ρ ρ)) 0 0 1) = _
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adj_bl, adj_zero, adj_zero, adj_one, GlobalTheory.MixModel.adj_smul, adj_one]
  congr 1
  · rw [hy]
    exact (blockMatrix_conj_upperUnipotent hn (a u) (a (-u)) hau y).symm
  · rw [neg_neg, hadjA, hadjA, hy]
    have := blockMatrix_conj_lowerUnipotent hn (cA D (a u)) (cA D (a (-u))) hcu (-adj y)
    rw [this]
    congr 2
    rw [GlobalTheory.MixModel.adj_smul, smul_neg]

theorem exists_shear_bound (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (θ : InfFam D) (hθ : IsInfFam θ)
    (H : G D n → ℝ≥0) (hH : IsHt H) (hC : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    (Φ : Mx D ρ p → ℂ) (hΦ : Φ ∈ schwartzA θ ρ p) :
    ∃ (A : ℝ) (N : ℕ), 0 < A ∧ ∀ (x : G D n) (y : Mx D ρ p), Φ y ≠ 0 →
      (H (x * M.sh y) : ℝ) ≤ A * rr (fun τ i j => compAt θ τ y i j) ^ N * (H x : ℝ) := by
  obtain ⟨e, hec, hea, hes⟩ := dil_exists D θ hθ n ρ p hn M
  obtain ⟨S, hS, hsupp⟩ := exists_compact_fin D θ ρ p Φ hΦ
  obtain ⟨e0, he0⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ ρ p
  have hB : IsCompact (e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) :=
    ((isCompact_closedBall _ _).prod isCompact_singleton).image e0.symm.continuous
  have hCf : IsCompact (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S)) :=
    (isCompact_singleton.prod hS).image e0.symm.continuous
  obtain ⟨κ₀, hκ₀, hb₀⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC _ ((hB.union hCf).image M.sh_cont)
  obtain ⟨κ₁, hκ₁, hb₁⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC _
    (isCompact_Icc.image hec : IsCompact (e '' Set.Icc (-1 : ℝ) 1))
  have hpw := pow_bound (fun x => (H x : ℝ)) e hea κ₁ hκ₁ (fun u hu x => hb₁ _ ⟨u, hu, rfl⟩ x) (fun x => NNReal.coe_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log κ₁)
  have hκE : κ₁ ≤ Real.exp N := by
    calc κ₁ = Real.exp (Real.log κ₁) := (Real.exp_log (lt_of_lt_of_le one_pos hκ₁)).symm
      _ ≤ _ := Real.exp_le_exp.2 hN

  have hg : ∀ (r : ℝ), 1 ≤ r → ∀ u, |u| = Real.log r → ∀ x, (H (x * e u) : ℝ) ≤ Real.exp N * r ^ N * (H x : ℝ) := by
    intro r hr u hu x
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    have hl : 0 ≤ Real.log r := Real.log_nonneg hr
    have h1 := hpw ⌈|u|⌉₊ u (Nat.le_ceil _) x
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _))
    have hc : (⌈|u|⌉₊ : ℝ) ≤ Real.log r + 1 := by
      have h := Nat.ceil_lt_add_one (abs_nonneg u)
      exact h.le.trans (by rw [hu])
    calc κ₁ ^ ⌈|u|⌉₊ ≤ Real.exp N ^ ⌈|u|⌉₊ := pow_le_pow_left₀ (zero_le_one.trans hκ₁) hκE _
      _ = Real.exp ((N : ℝ) * (⌈|u|⌉₊ : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp ((N : ℝ) * (Real.log r + 1)) := Real.exp_le_exp.2 (by gcongr)
      _ = Real.exp N * r ^ N := by
        rw [mul_add, mul_one, Real.exp_add, mul_comm, mul_comm (N : ℝ), Real.exp_mul, Real.exp_log hr0, Real.rpow_natCast]
  refine ⟨κ₀ ^ 2 * Real.exp N ^ 2, 2 * N, by positivity, fun x y hy => ?_⟩
  set z : D.what₂.Tau → Fin ρ → Fin p → ℂ := fun τ i j => compAt θ τ y i j with hz
  set f : Fin ρ → Fin p → Af D.host.F ⊗[D.host.F] D.host.E := fun i j => finPart D (y i j) with hf
  have hey : e0 y = (z, f) := he0 y
  set r := rr z with hr
  have hr1 : 1 ≤ r := one_le_rr z
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  set y₀ := e0.symm (r⁻¹ • z, 0) with hy₀
  set y₁ := e0.symm (z, 0) with hy₁
  set y₂ := e0.symm (0, f) with hy₂
  have hsum : y = y₁ + y₂ := by
    apply e0.injective
    rw [map_add, hy₁, hy₂, e0.apply_symm_apply, e0.apply_symm_apply, hey]
    simp
  have hc₀ : ∀ τ i j, compAt θ τ y₀ i j = r⁻¹ • z τ i j := fun τ i j => by
    have := congrArg Prod.fst (he0 y₀)
    rw [hy₀, e0.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) i) j).symm
  have hc₁ : ∀ τ i j, compAt θ τ y₁ i j = z τ i j := fun τ i j => by
    have := congrArg Prod.fst (he0 y₁)
    rw [hy₁, e0.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) i) j).symm
  have hf₀ : ∀ i j, finPart D (y₀ i j) = 0 := fun i j => by
    have := congrArg Prod.snd (he0 y₀)
    rw [hy₀, e0.apply_symm_apply] at this
    exact (congrFun (congrFun this i) j).symm
  have hf₁ : ∀ i j, finPart D (y₁ i j) = 0 := fun i j => by
    have := congrArg Prod.snd (he0 y₁)
    rw [hy₁, e0.apply_symm_apply] at this
    exact (congrFun (congrFun this i) j).symm
  have hsh₁ : M.sh y₁ = e (Real.log r) * M.sh y₀ * e (-Real.log r) := by
    refine hes _ y₀ y₁ (fun τ i j => ?_) (fun i j => by rw [hf₀, hf₁])
    rw [hc₀, hc₁, Real.exp_log hr0, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast hr0.ne'), one_mul]
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hy₀B : M.sh y₀ ∈ M.sh '' ((e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) ∪
      (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S))) := by
    refine ⟨y₀, Or.inl ⟨(r⁻¹ • z, 0), ⟨?_, rfl⟩, rfl⟩, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
    exact inv_mul_le_one_of_le₀ (norm_le_rr z) hr0.le
  have hy₂C : M.sh y₂ ∈ M.sh '' ((e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) ∪
      (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S))) :=
    ⟨y₂, Or.inr ⟨(0, f), ⟨rfl, hsupp y hy⟩, rfl⟩, rfl⟩
  have hexp : M.sh y = e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂ := by
    rw [← hsh₁, GlobalTheory.CompanionTheory.FJE.sh_add, ← hsum]
  have hE : 0 ≤ Real.exp N * r ^ N := by positivity
  have hκ₀' : 0 ≤ κ₀ := zero_le_one.trans hκ₀
  have s1 := hb₀ _ hy₂C (x * e (Real.log r) * M.sh y₀ * e (-Real.log r))
  have s2 := hg r hr1 (-Real.log r) (by rw [abs_neg, abs_of_nonneg hl]) (x * e (Real.log r) * M.sh y₀)
  have s3 := hb₀ _ hy₀B (x * e (Real.log r))
  have s4 := hg r hr1 (Real.log r) (abs_of_nonneg hl) x
  have e1 : x * M.sh y = x * e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂ := by
    rw [hexp]; simp only [mul_assoc]
  rw [e1]
  calc (H (x * e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂) : ℝ)
      ≤ κ₀ * (Real.exp N * r ^ N * (κ₀ * (Real.exp N * r ^ N * (H x : ℝ)))) := by
        refine s1.trans (mul_le_mul_of_nonneg_left ?_ hκ₀')
        refine s2.trans (mul_le_mul_of_nonneg_left ?_ hE)
        exact s3.trans (mul_le_mul_of_nonneg_left s4 hκ₀')
    _ = κ₀ ^ 2 * Real.exp N ^ 2 * r ^ (2 * N) * (H x : ℝ) := by ring

theorem height_shear_majorant : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (θ : InfFam D), IsInfFam θ →
  ∀ H : G D n → ℝ≥0, IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ Φ ∈ schwartzA θ ρ p, ∀ τ : ℝ, 0 ≤ τ → ∃ W : Mx D ρ p → ℝ, Integrable W m.μ ∧
    ∀ (x : G D n) (y : Mx D ρ p), (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ W y * (H x : ℝ) ^ τ := by
  intro D n ρ p hn M m θ hθ H hH hC Φ hΦ τ hτ
  obtain ⟨A, N, hA, hb⟩ := exists_shear_bound D n ρ p hn M θ hθ H hH hC Φ hΦ
  set L := ⌈(N : ℝ) * τ⌉₊ with hL
  have hmem := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ ρ p _ (rr_temperate (ι := D.what₂.Tau) (a := ρ) (b := p) L) Φ hΦ
  have hint := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ ρ p m.μ m.𝓕 m.hμ _ hmem
  refine ⟨fun y => A ^ τ * ‖((rr (fun τ i j => compAt θ τ y i j) : ℝ) : ℂ) ^ L * Φ y‖, hint.norm.const_mul _, fun x y => ?_⟩
  have hH0 : ∀ g, (0 : ℝ) ≤ (H g : ℝ) := fun g => NNReal.coe_nonneg _
  by_cases hy : Φ y = 0
  · simp [hy]
  set r := rr (fun τ i j => compAt θ τ y i j) with hr
  have hr1 : 1 ≤ r := one_le_rr _
  have hr0 : 0 ≤ r := by linarith
  have h1 : (H (x * M.sh y) : ℝ) ^ τ ≤ (A * r ^ N * (H x : ℝ)) ^ τ :=
    Real.rpow_le_rpow (hH0 _) (hb x y hy) hτ
  have h2 : (A * r ^ N * (H x : ℝ)) ^ τ = A ^ τ * (r ^ N) ^ τ * (H x : ℝ) ^ τ := by
    rw [Real.mul_rpow (by positivity) (hH0 _), Real.mul_rpow hA.le (by positivity)]
  have h3 : (r ^ N) ^ τ ≤ r ^ L := by
    rw [← Real.rpow_natCast r N, ← Real.rpow_mul hr0, ← Real.rpow_natCast r L]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (Nat.le_ceil _)
  have h4 : ‖((r : ℝ) : ℂ) ^ L * Φ y‖ = r ^ L * ‖Φ y‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  show _ ≤ A ^ τ * ‖((r : ℝ) : ℂ) ^ L * Φ y‖ * _
  rw [h4]
  have hAτ : 0 ≤ A ^ τ := Real.rpow_nonneg hA.le _
  have hHτ : 0 ≤ (H x : ℝ) ^ τ := Real.rpow_nonneg (hH0 _) _
  calc (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ (A ^ τ * (r ^ N) ^ τ * (H x : ℝ) ^ τ) * ‖Φ y‖ := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (A ^ τ * r ^ L * (H x : ℝ) ^ τ) * ‖Φ y‖ := by gcongr
    _ = A ^ τ * (r ^ L * ‖Φ y‖) * (H x : ℝ) ^ τ := by ring

end GlobalTheory.CompanionTheory.ShearGrowth
end
