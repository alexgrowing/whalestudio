import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPartitionOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PoincareSeriesCompactSupportThetaLawStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaSplitApprox

theorem exists_slices {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (F : X × Y → ℂ) (hF : Continuous F) {C : Set X} {K : Set Y} (hC : IsCompact C) (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) : ∃ (n : ℕ) (a : Fin n → X) (π : Fin n → C(X, ℝ)),
      ∀ x ∈ C, ∀ y ∈ K, ‖F (x, y) - ∑ i, (π i x : ℂ) * F (a i, y)‖ ≤ ε := by
  have hV : ∀ a : X, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, ∀ y ∈ K, ‖F (x, y) - F (a, y)‖ < ε := by
    intro a
    have hn : IsOpen {p : X × Y | ‖F p - F (a, p.2)‖ < ε} :=
      isOpen_lt (hF.sub (hF.comp (continuous_const.prodMk continuous_snd))).norm continuous_const
    obtain ⟨u, v, hu, -, hau, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := a)) hK hn (by
      rintro ⟨x, y⟩ ⟨hx, -⟩
      obtain rfl : x = a := hx
      simpa using hε)
    exact ⟨u, hu, hau rfl, fun x hx y hy => @huv (x, y) ⟨hx, hKv hy⟩⟩
  choose V hVo hVm hVε using hV
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover V fun x _ => (hVo x).mem_nhds (hVm x)
  have hcov' : C ⊆ ⋃ i : Fin t.card, V (t.equivFin.symm i) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcov hz)
    exact Set.mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, by simpa using hzx⟩
  obtain ⟨π, hπs, hπ1, hπ01, -⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun i => hVo _) hC hcov'
  refine ⟨t.card, fun i => t.equivFin.symm i, π, fun x hx y hy => ?_⟩
  have h1 : ∑ i, π i x = 1 := by simpa using hπ1 hx
  have h2 : F (x, y) - ∑ i, (π i x : ℂ) * F (t.equivFin.symm i, y) =
      ∑ i, (π i x : ℂ) * (F (x, y) - F (t.equivFin.symm i, y)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
  rw [h2]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun i => π i x * ε) fun i _ => ?_).trans ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hπ01 i x).1]
    by_cases h0 : π i x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hVε _ x (hπs i (subset_tsupport _ h0)) y hy).le (hπ01 i x).1
  · rw [← Finset.sum_mul, h1, one_mul]

theorem norm_sub_sum_tsum_le {Γ ι : Type*} [Fintype ι] {c : Γ → ℝ} (hc0 : ∀ γ, 0 ≤ c γ) (hc1 : HasSum c 1)
    (hfin : {γ | c γ ≠ 0}.Finite) {φ G : Γ → ℂ} (hφ : ∀ γ, ‖φ γ‖ = 1) {z : ℂ} (hG : ∀ γ, φ γ * G γ = z)
    (p : ι → Γ → ℝ) (b : ι → ℂ) {ε : ℝ} (hε : ∀ γ, c γ ≠ 0 → ‖G γ - ∑ i, (p i γ : ℂ) * b i‖ ≤ ε) :
    ‖z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i‖ ≤ ε := by
  have h0 : ∀ γ ∉ hfin.toFinset, c γ = 0 := fun γ hγ => by simpa using hγ
  have h1 : ∑ γ ∈ hfin.toFinset, c γ = 1 := (hasSum_sum_of_ne_finset_zero h0).unique hc1
  have h2 : ∀ i, ∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ) = ∑ γ ∈ hfin.toFinset, φ γ * ((c γ * p i γ : ℝ) : ℂ) :=
    fun i => tsum_eq_sum fun γ hγ => by simp [h0 γ hγ]
  have h3 : z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i =
      ∑ γ ∈ hfin.toFinset, (c γ : ℂ) * (φ γ * (G γ - ∑ i, (p i γ : ℂ) * b i)) := by
    simp only [h2, mul_sub, hG, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [h3]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun γ => c γ * ε) fun γ hγ => ?_).trans ?_)
  · rw [norm_mul, norm_mul, hφ, one_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 γ)]
    exact mul_le_mul_of_nonneg_left (hε γ (by simpa using hγ)) (hc0 γ)
  · rw [← Finset.sum_mul, h1, one_mul]

theorem exists_approx : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B)
    (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → WO A T → ℂ) (g : Fin n → WO B T → ℂ),
      (∀ i, Continuous (P i)) ∧
      (∀ i (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T),
        P i (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * P i u) ∧
      (∀ i, IsThetaFunO ψ B T (g i)) ∧
      ∀ w, ‖f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε := by
  intro D ψ hψ S A B T o f hf ε hε
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨-, a2, -, a4, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := lattice_Mx D T.rank B.rank
  have hFc : Continuous fun p : WO A T × WO B T => f ((o.resS T).symm p) := hf.cont.comp (o.continuous_resS_symm T)
  obtain ⟨hA, hB⟩ := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
  obtain ⟨χ, hχc, hχs, hχ0, hχ1⟩ := GlobalTheory.RatPartition.exists_partition_one D A T
  obtain ⟨n, a, π, hπ⟩ := exists_slices _ hFc (C := tsupport χ) hχs hK hε

  have hπ' : ∀ x ∈ tsupport χ, ∀ y,
      ‖f ((o.resS T).symm (x, y)) - ∑ i, (π i x : ℂ) * f ((o.resS T).symm (a i, y))‖ ≤ ε := by
    intro x hx y
    obtain ⟨γ, hγ, hγK⟩ := hKc y
    obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
    have law : ∀ u, f ((o.resS T).symm (u, rat γ₀ + y)) =
        ψ (-(symplOH B T (ratW T B γ₀) y)) * f ((o.resS T).symm (u, y)) := fun u => (hB u).quasi γ₀ y
    have h := hπ x hx _ hγK
    simp only [law] at h
    simp only [mul_left_comm _ (ψ _)] at h
    rwa [← Finset.mul_sum, ← mul_sub, norm_mul, hn, one_mul] at h
  have hper := fun i => GlobalTheory.T.poincareSeries_compactSupport_thetaLaw D ψ hψ A T (fun z => ((χ z * π i z : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hχc.mul (π i).continuous))
    ((HasCompactSupport.mul_right (f' := fun z => π i z) hχs).comp_left Complex.ofReal_zero)
  have hfin := (GlobalTheory.T.poincareSeries_compactSupport_thetaLaw D ψ hψ A T (fun z => ((χ z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hχc)
    (hχs.comp_left Complex.ofReal_zero)).1
  refine ⟨n, _, fun i v => f ((o.resS T).symm (a i, v)), fun i => (hper i).2.1, fun i γ u => (hper i).2.2 γ u,
    fun i => hB (a i), fun w => ?_⟩
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective w
  rw [AddEquiv.apply_symm_apply]
  refine norm_sub_sum_tsum_le (c := fun γ => χ (ratW T A γ + u)) (fun _ => hχ0 _) (hχ1 u) (by simpa using hfin u)
    (G := fun γ => f ((o.resS T).symm (ratW T A γ + u, v))) (fun _ => hn _) (fun γ => ?_)
    (fun i γ => π i (ratW T A γ + u)) _ fun γ hγ => hπ' _ (subset_tsupport _ hγ) v
  have law := (hA v).quasi γ u
  beta_reduce at law ⊢
  rw [law, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaSplitApprox

end
