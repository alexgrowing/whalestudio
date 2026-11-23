import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelicStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatioStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaK

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatCount

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def ratHom (M : ℕ) : (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun := ratTup (AF F)
  map_zero' := by
    funext a i
    simp [ratTup]
  map_add' X Y := by
    funext a i
    simp [ratTup]

lemma box_mono {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

lemma sizeInf_nonneg {d : ℕ} (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma repr_projInf_ratTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf (ratTup (AF F) X) a i) k =
      algebraMap F (Ainf F) (b.repr (X a i) k) := by
  have : projInf (ratTup (AF F) X) a i = (1 : Ainf F) ⊗ₜ[F] X a i := by
    simp [projInf, ratTup, inclR]
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma sizeTup_ratTup_pos {d M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → E)
    (hX : X ≠ 0) : 0 < sizeTup b (projInf (ratTup (AF F) X)) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨k, hk⟩ : ∃ k, b.repr (X a i) k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hi (b.repr.map_eq_zero_iff.mp (Finsupp.ext h))
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  set Y := projInf (ratTup (AF F) X : Fin n → Fin M → AF F ⊗[F] E) with hY
  have h1 : 0 < ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ := by
    rw [hY, repr_projInf_ratTup, norm_pos_iff]
    change algebraMap F v.Completion (b.repr (X a i) k) ≠ 0
    exact (map_ne_zero _).mpr hk
  have h2 : ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖ ≤ sizeInf b (Y a i) :=
    (Finset.single_le_sum
      (f := fun v => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ v)).trans
    (Finset.single_le_sum
      (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k v‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have h3 : sizeInf b (Y a i) ≤ sizeTup b Y :=
    (Finset.single_le_sum (f := fun i => sizeInf b (Y a i))
      (fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (Y a i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sizeInf_nonneg b _) (Finset.mem_univ a))
  linarith

end SlopeTestRemainingChoices

lemma exists_pos_lt {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ S, r < f x :=
  _root_.Bl.FirstLemmaK.goal1 hS f hf

theorem count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E)), IsCompact Ω → ∃ x₀ C : ℝ, ∀ x : ℝ, ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1) ≤ if x < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * M * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M Ω hΩ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨hcpt, hexh, hflow⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ b 1 M
  obtain ⟨-, hfin, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hCM 1 M
  obtain ⟨N, r, hN, hr, hsub⟩ := hexh Ω hΩ

  obtain ⟨r₀, h0, h1, hsmall⟩ := exists_pos_lt
    (((hfin _ (hcpt N 1 hN)).subset (Set.inter_subset_left
      (t := {X : Fin 1 → Fin M → E | X ≠ 0}))))
    (fun X => sizeTup b (projInf (ratTup (AF F) X)))
    (fun X hX => sizeTup_ratTup_pos b X hX.2)
  have hnone : ∀ X : Fin 1 → Fin M → E, X ≠ 0 → ratTup (AF F) X ∉ box b N r₀ := by
    intro X hX hmem
    have := hsmall X ⟨box_mono b N h1 hmem, hX⟩
    exact absurd hmem.2 (not_le.mpr this)
  have hscale : ∀ (x : ℝ) (Y : Fin 1 → Fin M → AF F ⊗[F] E),
      ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ Ω →
        Y ∈ box b N (Real.exp x * r) := by
    intro x Y hY
    refine (hflow τ hτ N (Real.exp x * r) (-x) Y).mp ?_
    have : Real.exp (-x) * (Real.exp x * r) = r := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact hsub hY
  refine ⟨Real.log (r₀ / r), (5 * r / r₀) ^ (2 * Module.finrank ℚ F * M), fun x => ?_⟩
  split_ifs with hx
  ·
    have hlt : Real.exp x * r < r₀ := by
      have := (Real.lt_log_iff_exp_lt (div_pos h0 hr)).mp hx
      exact (lt_div_iff₀ hr).mp this
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun X => Set.indicator_of_notMem ?_ _)
    intro hmem
    exact hnone X.1 X.2 (box_mono b N hlt.le (hscale x _ hmem))
  · have hge : r₀ ≤ Real.exp x * r := by
      have := (Real.log_le_iff_le_exp (div_pos h0 hr)).mp (not_lt.mp hx)
      exact (div_le_iff₀ hr).mp this
    set e := ratHom (F := F) (E := E) M with he
    have hone : ∑' l : Fin 1 → Fin M → E,
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ 1 := by
      rw [tsum_eq_single 0]
      · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => by simp)
      · intro X hX
        exact Set.indicator_of_notMem (hnone X hX) _
    have hpack := GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hCM _ b M (Fin 1 → Fin M → E) e N r₀ (Real.exp x * r) h0 hge
    calc ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0}, (Set.indicator Ω (fun _ => (1 : ℝ≥0∞)))
            (((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • ratTup (AF F) X.1)
        ≤ ∑' X : {X : Fin 1 → Fin M → E // X ≠ 0},
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e X.1) := by
          refine ENNReal.tsum_le_tsum fun X => ?_
          by_cases hm : ((τ (Multiplicative.ofAdd (-x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
              ratTup (AF F) X.1 ∈ Ω
          · have hm' : e X.1 ∈ box b N (Real.exp x * r) := hscale x _ hm
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
          · rw [Set.indicator_of_notMem hm]
            exact bot_le
      _ ≤ ∑' l : Fin 1 → Fin M → E,
            (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun l => (Set.indicator (box b N (Real.exp x * r)) (fun _ => (1 : ℝ≥0∞))) (e l))
      _ ≤ ENNReal.ofReal ((5 * (Real.exp x * r) / r₀) ^ (2 * Module.finrank ℚ F * M)) * 1 :=
          hpack.trans (mul_le_mul_right hone _)
      _ = ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M) *
            Real.exp (2 * Module.finrank ℚ F * M * x)) := by
          rw [mul_one]
          congr 1
          have : (2 * (Module.finrank ℚ F : ℝ) * M * x) =
              ((2 * Module.finrank ℚ F * M : ℕ) : ℝ) * x := by push_cast; ring
          rw [this, Real.exp_nat_mul, ← mul_pow]
          congr 1
          ring

end GlobalTheory.CompanionTheory.SW.LatCount
