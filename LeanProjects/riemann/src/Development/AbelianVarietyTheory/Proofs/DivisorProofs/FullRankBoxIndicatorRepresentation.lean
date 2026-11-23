import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

noncomputable section
namespace GlobalTheory.RankChart.Extend
open ValuativeRel GlobalTheory.LocMod.Inhab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valuation_lt (b : kˣ) : IsOpen {x : k | valuation k x < valuation k (b : k)} := by
  let H : AddSubgroup k :=
    { carrier := {x | valuation k x < valuation k (b : k)}
      zero_mem' := by simp [zero_lt_iff]
      add_mem' := fun {x y} hx hy => show valuation k (x + y) < _ from lt_of_le_of_lt (Valuation.map_add _ x y) (max_lt hx hy)
      neg_mem' := fun {x} hx => by simpa using hx }
  have hH : (H : Set k) ∈ nhds (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 (valuation k (b : k)) (by simp), fun x hx => hx⟩
  exact H.isOpen_of_mem_nhds hH

variable {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D]

theorem isCompact_sphere (b : kˣ) :
    IsCompact ((box T R b : Set (Matrix T R k)) ∩ {C | ∀ t i, valuation k (C t i) < valuation k (b : k)}ᶜ) := by
  refine (isCompact_box b).inter_right (IsOpen.isClosed_compl ?_)
  have : {C : Matrix T R k | ∀ t i, valuation k (C t i) < valuation k (b : k)} =
      Set.pi Set.univ fun _ : T => Set.pi Set.univ fun _ : R => {x : k | valuation k x < valuation k (b : k)} := by
    ext C
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valuation_lt b

theorem exists_box_of_mul_mem {K : Set (Matrix R D k)} (hK : IsCompact K)
    (hinj : ∀ Y₁ ∈ K, ∀ C : Matrix T R k, C * Y₁ = 0 → C = 0) (b : kˣ) :
    ∃ N : kˣ, ∀ Y₁ ∈ K, ∀ C : Matrix T R k, C * Y₁ ∈ box T D N → C ∈ box T R b := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  set Sph : Set (Matrix T R k) := (box T R b : Set (Matrix T R k)) ∩
    {C | ∀ t i, valuation k (C t i) < valuation k (b : k)}ᶜ with hSph
  set E : Set (Matrix T D k) := (fun p : Matrix R D k × Matrix T R k => p.2 * p.1) '' (K ×ˢ Sph) with hE
  have hEc : IsCompact E := (hK.prod (isCompact_sphere b)).image (by fun_prop)
  have h0 : (0 : Matrix T D k) ∉ E := by
    rintro ⟨⟨Y₁, C⟩, ⟨hY, hC⟩, h⟩
    have := hinj Y₁ hY C h
    subst this
    exact hC.2 fun t i => by simp [zero_lt_iff]
  obtain ⟨N, hN⟩ := exists_box_subset (hEc.isClosed.isOpen_compl.mem_nhds h0)
  refine ⟨N, fun Y₁ hY C hC => ?_⟩
  by_contra hCb
  obtain ⟨r, q, hrq⟩ : ∃ r q, valuation k (b : k) < valuation k (C r q) := by
    by_contra hh
    push Not at hh
    exact hCb hh
  obtain ⟨⟨t, i⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (T × R))
    (fun p => valuation k (C p.1 p.2)) ⟨(r, q), Finset.mem_univ _⟩
  have hbc : valuation k (b : k) < valuation k (C t i) := hrq.trans_le (hmax (r, q) (Finset.mem_univ _))
  have hb0 : valuation k (b : k) ≠ 0 := by simp
  have hc0 : valuation k (C t i) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hbc)
  have hc : C t i ≠ 0 := by simpa using hc0
  have hle : valuation k ((b : k) / C t i) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hc0)]; exact hbc.le
  have hmem : ((b : k) / C t i) • C ∈ Sph := by
    refine ⟨fun t' i' => ?_, fun h => ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_div₀]
      calc valuation k (b : k) / valuation k (C t i) * valuation k (C t' i')
          ≤ valuation k (b : k) / valuation k (C t i) * valuation k (C t i) :=
            mul_le_mul_right (hmax (t', i') (Finset.mem_univ _)) _
        _ = valuation k (b : k) := div_mul_cancel₀ _ hc0
    · have := h t i
      rw [Matrix.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hc] at this
      exact lt_irrefl _ this
  have hin : ((b : k) / C t i) • C * Y₁ ∈ E := ⟨(Y₁, _), ⟨hY, hmem⟩, rfl⟩
  apply hN (((b : k) / C t i) • C * Y₁) _ hin
  intro r' q'
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul]
  exact (mul_le_of_le_one_left' hle).trans (hC r' q')

end GlobalTheory.RankChart.Extend

namespace GlobalTheory.RankChart.Extend
open ValuativeRel GlobalTheory.LocMod.Inhab

theorem eq_zero_of_mul_eq_zero {k R T D : Type} [Field k] [Fintype R] [Fintype T] [Fintype D]
    {Y₁ : Matrix R D k} (hY : Y₁.rank = Fintype.card R) {C : Matrix T R k} (h : C * Y₁ = 0) : C = 0 := by
  have hli : LinearIndependent k Y₁.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hY]
  ext t i
  have := Fintype.linearIndependent_iff.1 hli (fun i => C t i) (by
    funext j
    have := congrFun (congrFun h t) j
    simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.row] using this) i
  simpa using this

theorem continuous_fromRows {k R T D : Type} [TopologicalSpace k] :
    Continuous fun p : Matrix R D k × Matrix T D k => Matrix.fromRows p.1 p.2 := by
  refine continuous_pi fun i => ?_
  rcases i with i | i
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd

theorem exists_sb_extension : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ d : ℕ) (T : Type) [Fintype T] [DecidableEq T] (b : kˣ), ∀ θ ∈ fullRk k ρ d,
    ∃ Θ ∈ SB (Matrix (Fin ρ ⊕ T) (Fin d) k), ∀ Y : Matrix (Fin ρ ⊕ T) (Fin d) k, Y.rank ≤ ρ →
      Θ Y = Set.indicator {Z : Matrix (Fin ρ ⊕ T) (Fin d) k | ∃ C ∈ GlobalTheory.LocMod.Inhab.box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁}
        (fun Z => θ Z.toRows₁) Y := by
  intro k _ _ _ _ ρ d T _ _ b θ hθ
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨⟨hlc, hcs⟩, hrk⟩ := hθ
  set K := tsupport θ with hKdef
  have hsupp : IsClosed (Function.support θ) := (hlc.isOpen_fiber 0).isClosed_compl
  have hK : ∀ Y₁ ∈ K, θ Y₁ ≠ 0 := fun Y₁ h => by
    rw [hKdef, tsupport, hsupp.closure_eq] at h; exact h
  have hKrk : ∀ Y₁ ∈ K, Y₁.rank = ρ := fun Y₁ h => by
    by_contra hne; exact hK Y₁ h (hrk Y₁ hne)
  obtain ⟨N, hN⟩ := exists_box_of_mul_mem (T := T) (D := Fin d) (hcs : IsCompact K)
    (fun Y₁ h C hC => eq_zero_of_mul_eq_zero (by rw [hKrk Y₁ h, Fintype.card_fin]) hC) b
  obtain ⟨a, ha1, ha2⟩ : ∃ a : kˣ, valuation k (a : k) ≤ valuation k (N : k) ∧
      valuation k (b : k) * valuation k (a : k) ≤ valuation k (N : k) := by
    by_cases hb : valuation k (b : k) ≤ 1
    · exact ⟨N, le_rfl, mul_le_of_le_one_left' hb⟩
    · have hb0 : valuation k (b : k) ≠ 0 := by simp
      refine ⟨N * b⁻¹, ?_, ?_⟩
      · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
        refine mul_le_of_le_one_right' ?_
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hb))
      · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, mul_assoc,
          inv_mul_cancel₀ hb0, mul_one]
  set S : Set (Matrix (Fin ρ ⊕ T) (Fin d) k) :=
    {Y | ∃ C ∈ box T (Fin ρ) b, Y.toRows₂ - C * Y.toRows₁ ∈ box T (Fin d) N} with hS
  have hshift : ∀ Y E : Matrix (Fin ρ ⊕ T) (Fin d) k, E ∈ box (Fin ρ ⊕ T) (Fin d) a → Y ∈ S → Y + E ∈ S := by
    rintro Y E hE ⟨C, hC, hY⟩
    refine ⟨C, hC, ?_⟩
    have e : (Y + E).toRows₂ - C * (Y + E).toRows₁ =
        (Y.toRows₂ - C * Y.toRows₁) + (E.toRows₂ - C * E.toRows₁) := by
      rw [show (Y + E).toRows₂ = Y.toRows₂ + E.toRows₂ from rfl, show (Y + E).toRows₁ = Y.toRows₁ + E.toRows₁ from rfl,
        Matrix.mul_add]; abel
    rw [e]
    refine (box T (Fin d) N).add_mem hY ((box T (Fin d) N).sub_mem (fun t j => (hE (Sum.inr t) j).trans ha1) ?_)
    intro t j
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [map_mul]
    exact (mul_le_mul' (hC t i) (hE (Sum.inl i) j)).trans ha2
  have hiff : ∀ Y E : Matrix (Fin ρ ⊕ T) (Fin d) k, E ∈ box (Fin ρ ⊕ T) (Fin d) a → (Y + E ∈ S ↔ Y ∈ S) :=
    fun Y E hE => ⟨fun h => by simpa using hshift (Y + E) (-E) ((box _ _ a).neg_mem hE) h, hshift Y E hE⟩
  have hc1 : Continuous fun Y : Matrix (Fin ρ ⊕ T) (Fin d) k => Y.toRows₁ := by
    unfold Matrix.toRows₁; fun_prop
  refine ⟨S.indicator fun Z => θ Z.toRows₁, ⟨?_, ?_⟩, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    refine ⟨{Z | θ Z.toRows₁ = θ Y.toRows₁} ∩ {Z | Z - Y ∈ box (Fin ρ ⊕ T) (Fin d) a},
      ((hlc.comp_continuous hc1).isOpen_fiber _).inter ((isOpen_box a).preimage (by fun_prop)),
      ⟨rfl, by simp⟩, fun Z ⟨h1, h2⟩ => ?_⟩
    have hZ : Z ∈ S ↔ Y ∈ S := by
      have := hiff Y (Z - Y) h2
      rwa [add_sub_cancel] at this
    by_cases hY : Y ∈ S
    · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hZ.2 hY)]; exact h1
    · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt hZ.1 hY)]
  · have hcont : Continuous (fun p : (Matrix (Fin ρ) (Fin d) k × Matrix T (Fin ρ) k) × Matrix T (Fin d) k =>
        Matrix.fromRows p.1.1 (p.1.2 * p.1.1 + p.2)) :=
      continuous_fromRows.comp (by fun_prop : Continuous fun p : (Matrix (Fin ρ) (Fin d) k × Matrix T (Fin ρ) k) ×
        Matrix T (Fin d) k => (p.1.1, p.1.2 * p.1.1 + p.2))
    refine HasCompactSupport.intro (((hcs.prod (isCompact_box b)).prod (isCompact_box N)).image hcont) ?_
    intro Y hY
    by_contra h0
    have hYS : Y ∈ S := by by_contra hn; exact h0 (Set.indicator_of_notMem hn _)
    have hθY : θ Y.toRows₁ ≠ 0 := by rwa [Set.indicator_of_mem hYS] at h0
    obtain ⟨C, hC, hE⟩ := hYS
    refine hY ⟨((Y.toRows₁, C), Y.toRows₂ - C * Y.toRows₁), ⟨⟨subset_tsupport _ hθY, hC⟩, hE⟩, ?_⟩
    show Matrix.fromRows _ _ = Y
    rw [add_sub_cancel, Matrix.fromRows_toRows]
  · intro Y hYr
    by_cases hz : θ Y.toRows₁ = 0
    · simp only [Set.indicator, hz, ite_self]
    have hY1 : Y.toRows₁ ∈ K := subset_tsupport _ hz
    have hrk1 : Y.toRows₁.rank = ρ := hKrk _ hY1
    have hmem : Y ∈ S ↔ ∃ C ∈ box T (Fin ρ) b, Y.toRows₂ = C * Y.toRows₁ := by
      constructor
      · rintro ⟨C, hC, hE⟩
        have hT : ρ ≤ (Y.toRows₁)ᵀ.rank := by rw [Matrix.rank_transpose, hrk1]
        obtain ⟨τ, hτ⟩ := GlobalTheory.exists_rows_linearIndependent_of_le_rank ρ (Y.toRows₁)ᵀ hT
        have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
        have e : (Y.toRows₁)ᵀ.submatrix τ id = (Y.submatrix Sum.inl τ)ᵀ := by ext i j; rfl
        rw [e, Matrix.det_transpose] at hu
        obtain ⟨C', hC'⟩ := GlobalTheory.RankChart.exists_eq_stack k (Fin ρ) T (Fin d) τ Y
          (by rw [Fintype.card_fin]; exact hYr) hu.ne_zero
        have h2 : Y.toRows₂ = C' * Y.toRows₁ := by
          conv_lhs => rw [hC']
          simp [GlobalTheory.RankChart.stack]
        have hd : C' - C ∈ box T (Fin ρ) b := hN _ hY1 _ (by rw [Matrix.sub_mul, ← h2]; exact hE)
        refine ⟨C', ?_, h2⟩
        have := (box T (Fin ρ) b).add_mem hd hC
        rwa [sub_add_cancel] at this
      · rintro ⟨C, hC, h⟩
        exact ⟨C, hC, by rw [h, sub_self]; exact (box T (Fin d) N).zero_mem⟩
    by_cases hY : Y ∈ S
    · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (show Y ∈ {Z : Matrix (Fin ρ ⊕ T) (Fin d) k |
        ∃ C ∈ box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁} from hmem.1 hY)]
    · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (show Y ∉ {Z : Matrix (Fin ρ ⊕ T) (Fin d) k |
        ∃ C ∈ box T (Fin ρ) b, Z.toRows₂ = C * Z.toRows₁} from mt hmem.2 hY)]

end GlobalTheory.RankChart.Extend
