import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShellMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqRankOneFactorSL2OfGeometricOnShellsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThreeRankOneSphericalVectorCellValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDepthPowerLastSimpleReflectionCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningLastEven
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.CompanionTheory.InvStep

section Cell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem spherical_even (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : Even n) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (φ : GU σ n → ℂ) (hφ : IsSphericalU q (fun i => (α i : ℂ)) φ)
    (hφ1 : φ 1 = 1) :
    Integrable (fun u : cellU y => φ (y⁻¹ * u)) μ ∧ ∫ u : cellU y, φ (y⁻¹ * u) ∂μ = cSimpleU q k α := by
  have hq2 : 2 ≤ q := h.2.2.2.2.2.1
  let H : ℕ → Set (cellU y) := fun j => {u : cellU y |
    Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
      ((Multiplicative.ofAdd (j : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  have hHm : ∀ j, MeasurableSet (H j) := fun j => (shell_measure' L ϖ σ q h n k hk hn y hyK hy μ hμ j).1
  have hHμ : ∀ j, μ (H j) = (q : ENNReal) ^ j := fun j => by
    have := (shell_measure' L ϖ σ q h n k hk hn y hyK hy μ hμ j).2
    rw [zpow_natCast] at this; exact this
  have hmono : Monotone H := by
    intro i j hij u hu
    simp only [H, Set.mem_setOf_eq] at hu ⊢
    exact le_trans hu (WithZero.coe_le_coe.2 (Multiplicative.ofAdd_le.2 (by exact_mod_cast hij)))
  have hcov : ⋃ j, H j = Set.univ := by
    refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
    show ∃ j : ℕ, Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ _
    induction Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)
      using WithZero.recZeroCoe with
    | zero => exact ⟨0, zero_le'⟩
    | coe a =>
      refine ⟨(Multiplicative.toAdd a).toNat, WithZero.coe_le_coe.2 ?_⟩
      show Multiplicative.toAdd a ≤ ((Multiplicative.toAdd a).toNat : ℤ)
      exact Int.self_le_toNat _
  have hshape : ∀ u : cellU y, ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((((u : GU σ n)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j :=
    fun u => (GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff L σ n k hk hn y hy u).1 u.2
  have hval := fun u : cellU y =>
    GlobalTheory.T.sphericalVector_value_unitaryRankOne_gindikinKarpelevich L ϖ σ q h n k hk hn (fun i => (α i : ℂ)) φ hφ hφ1 y hyK hy u (hshape u)
  have hF0 : ∀ x ∈ H 0, φ (y⁻¹ * x) = 1 := by
    intro x hx
    rw [hval x, if_pos]
    simpa [H] using hx
  have hF : ∀ j x, x ∈ H (j + 1) → x ∉ H j → φ (y⁻¹ * x) = ((α k : ℂ) / q) ^ (j + 1) := by
    intro j x hx1 hx0
    have hv : Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) =
        ((Multiplicative.ofAdd (((j + 1 : ℕ)) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simp only [H, Set.mem_setOf_eq, not_le] at hx1 hx0
      revert hx1 hx0
      induction Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)
        using WithZero.recZeroCoe with
      | zero => intro _ h0; exact absurd h0 (not_lt.2 zero_le')
      | coe a =>
        intro h1 h0
        have h1' : Multiplicative.toAdd a ≤ ((j + 1 : ℕ) : ℤ) := WithZero.coe_le_coe.1 h1
        have h0' : (j : ℤ) < Multiplicative.toAdd a := WithZero.coe_lt_coe.1 h0
        congr 1
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        push_cast at h1' ⊢
        omega
    have hord := GlobalTheory.WeylCell.RankOneUnitary.ordL_of_v_eq _ _ hv
    have hnot : ¬ Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 := by
      rw [hv, ← WithZero.coe_one, WithZero.coe_le_coe]
      show ¬ (((j + 1 : ℕ) : ℤ) ≤ 0)
      omega
    rw [hval x, if_neg hnot, hord, neg_neg, zpow_natCast, zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv]
  obtain ⟨hInt1, hI1, -⟩ := GlobalTheory.T.integral_eq_rankOneFactorSL2_of_geometric_on_shells μ q hq2 (α k : ℂ) hαk H hHm hmono hcov hHμ (fun x => φ (y⁻¹ * x)) hF0 hF
  refine ⟨hInt1, ?_⟩
  rw [hI1]
  simp [cSimpleU, hk, hn]

theorem spherical_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (φ : GU σ n → ℂ) (hφ : IsSphericalU q (fun i => (α i : ℂ)) φ)
    (hφ1 : φ 1 = 1) :
    Integrable (fun u : cellU y => φ (y⁻¹ * u)) μ ∧ ∫ u : cellU y, φ (y⁻¹ * u) ∂μ = cSimpleU q k α := by
  by_cases hn : Even n
  · exact spherical_even h k hk hn y hyK hy μ hμ α hαk φ hφ hφ1
  · have hA := GlobalTheory.T.integral_depth_power_lastSimpleReflectionCell L ϖ σ q h n k hk hn y hyK hy μ hμ (α k) hαk
    have hpt : ∀ u : cellU y, φ (y⁻¹ * (u : GU σ n)) = ((α k : ℂ) / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) :=
      GlobalTheory.T.unitaryThreeRankOne_sphericalVector_cell_value L ϖ σ q h n k hk hn y hyK hy (fun i => (α i : ℂ)) φ hφ hφ1
    simp_rw [hpt]
    refine ⟨hA.1, ?_⟩
    rw [hA.2.1]
    simp [cSimpleU, hk, hn]

theorem cSimpleU_ne_zero (hq : 2 ≤ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (α : Fin (n / 2) → ℂˣ)
    (hαk : ‖(α k : ℂ)‖ < 1) : cSimpleU q k α ≠ 0 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hnq : ‖(q : ℂ)‖ = q := by simp
  set z : ℂ := ((α k : ℂˣ) : ℂ) with hz
  have key : ∀ (w : ℂ), ‖w‖ < 1 → 1 - w ≠ 0 := fun w hw e => by
    have : w = 1 := (sub_eq_zero.1 e).symm
    rw [this] at hw
    simp at hw
  have hqi : ‖(q : ℂ)⁻¹‖ < 1 := by
    rw [norm_inv, hnq]
    exact inv_lt_one_of_one_lt₀ hq1
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hαk two_ne_zero
  have hmul : ∀ a : ℂ, ‖a‖ ≤ 1 → ‖a * z‖ < 1 := fun a ha => by
    rw [norm_mul]
    calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by simpa using hαk
  have hqn : ‖(q : ℂ)⁻¹‖ ≤ 1 := hqi.le
  have hq2n : ‖((q : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, hnq]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
  simp only [cSimpleU, dif_neg hk]
  split_ifs with hn
  · exact div_ne_zero (key _ (hmul _ hqn)) (key _ hαk)
  · refine div_ne_zero (mul_ne_zero (key _ (hmul _ hq2n)) ?_) (key _ hz2)
    have := key (-((q : ℂ)⁻¹ * z)) (by rw [norm_neg]; exact hmul _ hqn)
    simpa using this

theorem scale_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∃ s : ℂ, (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * u * t) ∂μ = s * ∫ u : cellU y, F u ∂μ) ∧
      chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) * s = chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  by_cases hn : Even n
  · exact ⟨_, (conjScale' L ϖ σ q h n k hk hn y hyK hy μ hμ t ht).1, GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary L ϖ σ q h n k hk hn y hy α t ht⟩
  · refine ⟨_, (GlobalTheory.T.integral_diagonal_conj_lastSimpleReflectionCell L ϖ σ q h n k hk hn y hyK hy μ hμ t ht).1, ?_⟩
    obtain ⟨Φ, hΦ, hΦ1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
      (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    have e := GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor L ϖ σ q h n k hk hn y hyK hy α Φ hΦ t ht 1 y
    have hB := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t ht).1
    have e2 : Φ (y⁻¹ * t * 1 * y) = chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) := by
      have := hΦ (y⁻¹ * t * y) 1 1 hB (one_mem _)
      simpa [hΦ1, mul_assoc] using this
    rw [e2] at e
    simpa [hΦ1] using e

theorem shift_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂ) (ψ : GU σ n → ℂ) (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q α b * ψ g)
    (ν : GU σ n) (hν : IsUnipU ν) :
    ∫ u : cellU y, ψ (y⁻¹ * u * ν) ∂μ = ∫ u : cellU y, ψ (y⁻¹ * u) ∂μ := by
  by_cases hn : Even n
  · obtain ⟨u', hu', hsh⟩ := shiftEven L σ q n k hk hn α ψ hψ y hy ν hν
    have e : ∀ u : cellU y, ψ (y⁻¹ * u * ν) = ψ (y⁻¹ * (((⟨u', hu'⟩ : cellU y) * u : cellU y) : GU σ n)) := by
      intro u
      simpa using hsh u u.2 1
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v : cellU y => ψ (y⁻¹ * (v : GU σ n))) (⟨u', hu'⟩ : cellU y)
  · obtain ⟨p, hp⟩ := shiftOdd L ϖ σ q h n k hk hn y hyK hy α ψ hψ ν hν
    have e : ∀ u : cellU y, ψ (y⁻¹ * u * ν) = ψ (y⁻¹ * ((u * p : cellU y) : GU σ n)) := by
      intro u
      simpa using hp u 1
    simp_rw [e]
    exact (GlobalTheory.T.unitaryWeylCell_haar_rightTranslate_invariant L ϖ σ q h n k hk hn y hyK hy μ hμ p).1 fun w => ψ (y⁻¹ * w)

theorem integral_law (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (ψ : GU σ n → ℂ)
    (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q (fun i => (α i : ℂ)) b * ψ g)
    (β : GU σ n) (hβ : IsBorelU β) :
    ∫ u : cellU y, ψ (y⁻¹ * u * β) ∂μ =
      chiDeltaU q (fun i => (actU k α i : ℂ)) β * ∫ u : cellU y, ψ (y⁻¹ * u) ∂μ := by
  obtain ⟨t, ν, rfl, hν, htd, htdiag⟩ := GlobalTheory.T.unitaryBorel_eq_diagonal_mul_unipotent L σ n β hβ
  have hBt := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t htd).1
  obtain ⟨s, hs, hchi⟩ := scale_cell h k hk y hyK hy μ hμ α t htd
  have hχ : chiDeltaU q (fun i => (actU k α i : ℂ)) (t * ν) = chiDeltaU q (fun i => (actU k α i : ℂ)) t :=
    (GlobalTheory.WeylCell.RankOneUnitary.chiDeltaU_congr q _ t (t * ν) htdiag).symm
  have hpt : ∀ u : cellU y, ψ (y⁻¹ * u * (t * ν)) =
      chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) * ψ (y⁻¹ * (t⁻¹ * u * t) * ν) := by
    intro u
    rw [← hψ _ _ hBt]
    congr 1
    group
  simp_rw [hpt]
  rw [integral_const_mul, hs (fun v => ψ (y⁻¹ * v * ν)), ← mul_assoc, hchi, hχ,
    shift_cell h k hk y hyK hy μ hμ _ ψ hψ ν hν]

theorem integrable_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (ψ : GU σ n → ℂ)
    (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q (fun i => (α i : ℂ)) b * ψ g)
    (S : Set (GU σ n)) (hS : IsOpen S) (h1 : (1 : GU σ n) ∈ S) (hinv : ∀ g ∈ S, ∀ x, ψ (x * g) = ψ x) :
    Integrable (fun u : cellU y => ψ (y⁻¹ * u)) μ := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun g => by
    have hO : IsOpen ((fun x => g⁻¹ * x) ⁻¹' S) := hS.preimage (continuous_const.mul continuous_id)
    have hg : g ∈ (fun x => g⁻¹ * x) ⁻¹' S := by simpa using h1
    refine (tendsto_const_nhds (x := ψ g)).congr' (Filter.eventually_of_mem (hO.mem_nhds hg) fun x hx => ?_)
    have := hinv _ hx g
    rw [mul_inv_cancel_left] at this
    exact this.symm
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨Φ, hΦ, hΦ1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  obtain ⟨hI, -⟩ := spherical_cell h k hk y hyK hy μ hμ α hαk Φ hΦ hΦ1
  have hb : ∀ g, ‖ψ g‖ ≤ max C 0 * ‖Φ g‖ := by
    intro g
    obtain ⟨b, κ, hb, hκ, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ h.1 h.2.1 g
    have e2 := hΦ b 1 κ hb hκ
    rw [mul_one, hΦ1, mul_one] at e2
    rw [hψ b κ hb, e2, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC κ hκ).trans (le_max_left _ _)) (norm_nonneg _)
  refine (hI.norm.const_mul (max C 0)).mono'
    (hcont.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => hb _)

end Cell

theorem invStepU : PositivityTheory.SphericalProduct.InvStepU := by
  intro L _ _ _ ϖ σ q n h V _ _ ρ hadm hirr hsph χ j hj hχ f hf hfe
  have hk : ¬ j.val + 1 < n / 2 := by omega
  have hq2 : 2 ≤ q := h.2.2.2.2.2.1
  have hact : actU j χ = Function.update χ j (χ j)⁻¹ := by simp [actU, hk]
  rw [← hact]
  obtain ⟨-, ⟨y, hyK, hyw⟩, hμex⟩ := exists_data_U h n χ (simpleU j) (GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one n j).1
  letI : MeasurableSpace (cellU y) := borel _
  haveI : BorelSpace (cellU y) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμ⟩ := hμex y
  haveI := hμH
  have hlaw : ∀ (v : V) (b g : GU σ n), IsBorelU b →
      (f v).1 (b * g) = chiDeltaU q (fun i => (χ i : ℂ)) b * (f v).1 g := fun v b g hb => (f v).2 b g hb
  have htr : ∀ (g : GU σ n) (v : V) (x : GU σ n), (f (ρ g v)).1 x = (f v).1 (x * g) := fun g v x => by
    rw [hfe]
    rfl
  have hint : ∀ v : V, Integrable (fun u : cellU y => (f v).1 (y⁻¹ * u)) μ := fun v =>
    integrable_cell h j hk y hyK hyw μ hμ χ hχ _ (hlaw v) {g | ρ g v = v} (hadm.1 v) (by simp)
      fun g hg x => by rw [← htr, show ρ g v = v from hg]
  let lam : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ u : cellU y, (f v).1 (y⁻¹ * u) ∂μ
      map_add' := fun a b => by
        simp only [map_add, Submodule.coe_add, Pi.add_apply]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hlam : ∀ v, lam v = ∫ u : cellU y, (f v).1 (y⁻¹ * u) ∂μ := fun _ => rfl
  have hlamB : ∀ (b : GU σ n) (v : V), IsBorelU b →
      lam (ρ b v) = chiDeltaU q (fun i => (actU j χ i : ℂ)) b * lam v := by
    intro b v hb
    rw [hlam, hlam, ← integral_law h j hk y hyK hyw μ hμ χ _ (hlaw v) b hb]
    simp_rw [htr]
  let F : V →ₗ[ℂ] psSpaceU σ q (actU j χ) :=
    { toFun := fun v => ⟨fun g => lam (ρ g v), fun b g hb => by
        show lam (ρ (b * g) v) = _
        rw [map_mul, Module.End.mul_apply, hlamB b _ hb]⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by
        show lam (ρ g (a + b)) = lam (ρ g a) + lam (ρ g b)
        simp)
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        show lam (ρ g (c • a)) = c * lam (ρ g a)
        simp) }
  have hFe : ∀ (g : GU σ n) (v : V), F (ρ g v) = psFunU σ q (actU j χ) g (F v) := fun g v =>
    Subtype.ext (funext fun x => by
      show lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
      rw [map_mul, Module.End.mul_apply])

  obtain ⟨v₀, hv₀, hv₀0⟩ := (Submodule.ne_bot_iff _).1 hsph
  obtain ⟨Φ, hΦ, hΦ1, huniq⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
    (fun i => (χ i : ℂ)) fun i => (χ i).ne_zero
  have hsv : IsSphericalU q (fun i => (χ i : ℂ)) (f v₀).1 := by
    intro b g κ hb hκ
    rw [mul_assoc, hlaw v₀ b _ hb, ← htr, GlobalTheory.LGrp.mem_fixed.1 hv₀ κ hκ]
  have he := huniq _ hsv
  have hf0 : (f v₀).1 1 ≠ 0 := by
    intro h0
    apply hv₀0
    apply hf
    rw [map_zero]
    refine Subtype.ext ?_
    rw [he, h0]
    funext g
    simp
  have hlam0 : lam v₀ ≠ 0 := by
    have e : lam v₀ = (f v₀).1 1 * cSimpleU q j χ := by
      rw [hlam, ← (spherical_cell h j hk y hyK hyw μ hμ χ hχ Φ hΦ hΦ1).2, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he _)
    rw [e]
    exact mul_ne_zero hf0 (cSimpleU_ne_zero hq2 j hk χ hχ)
  let W : Subrepresentation ρ := ⟨LinearMap.ker F, fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hFe, hv, map_zero]⟩
  have hW : W = ⊥ := by
    refine (hirr.eq_bot_or_eq_top W).resolve_right fun hT => ?_
    have h1 : v₀ ∈ W.toSubmodule := by
      rw [hT]
      trivial
    have h2 : F v₀ = 0 := h1
    have h3 := congrFun (congrArg Subtype.val h2) 1
    apply hlam0
    have h4 : lam (ρ 1 v₀) = 0 := h3
    simpa using h4
  refine ⟨F, ?_, hFe⟩
  rw [← LinearMap.ker_eq_bot]
  have := congrArg Subrepresentation.toSubmodule hW
  exact this

end GlobalTheory.CompanionTheory.InvStep

end
