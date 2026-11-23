import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubPowLe
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

noncomputable section

namespace GlobalTheory.BigInt

section General

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_le_one_of_root {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {q : R[X]}
    (hq : q.Monic) {x : C} (hx : q.eval₂ f x = 0) : ‖x‖ ≤ 1 := by
  let v := NormedField.valuation (K := C)
  let g : R →+* v.integer := f.codRestrict v.integer fun r => hf r
  have hint : IsIntegral v.integer x := by
    refine ⟨q.map g, hq.map g, ?_⟩
    rw [eval₂_map]
    exact hx
  exact (Valuation.integer.integers v).mem_of_integral hint

def ints (F : Subfield C) : Subring C := F.toSubring ⊓ (NormedField.valuation (K := C)).integer

theorem mem_ints {F : Subfield C} {x : C} : x ∈ ints F ↔ x ∈ F ∧ ‖x‖ ≤ 1 := Iff.rfl

variable {F : Subfield C}

theorem div_mem_ints {x y : C} (hx : x ∈ F) (hy : y ∈ F) (h : ‖x‖ ≤ ‖y‖) : x / y ∈ ints F :=
  mem_ints.2 ⟨div_mem hx hy, by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩

theorem dvd_iff {x y : ints F} : y ∣ x ↔ ‖(x : C)‖ ≤ ‖(y : C)‖ := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_ints.1 z.2).2
  · intro h
    by_cases hy : (y : C) = 0
    · have : x = 0 := Subtype.ext (by simpa [hy] using h)
      rw [this]; exact dvd_zero _
    · refine ⟨⟨x / y, div_mem_ints (mem_ints.1 x.2).1 (mem_ints.1 y.2).1 h⟩, Subtype.ext ?_⟩
      simp only [Subring.coe_mul]
      field_simp

theorem not_isUnit_iff {x : ints F} : ¬ IsUnit x ↔ ‖(x : C)‖ < 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff]; simp

variable {π : ints F} (h0 : (π : C) ≠ 0) (h1 : ‖(π : C)‖ < 1)
  (hπ : ∀ y ∈ F, ‖y‖ < 1 → ‖y‖ ≤ ‖(π : C)‖)

include h0 h1 hπ

theorem irreducible_unif : Irreducible π := by
  refine ⟨not_isUnit_iff.2 h1, fun a b hab => ?_⟩
  by_contra hc
  rw [not_or, not_isUnit_iff, not_isUnit_iff] at hc
  have ha := hπ a (mem_ints.1 a.2).1 hc.1
  have e : ‖(π : C)‖ = ‖(a : C)‖ * ‖(b : C)‖ := by rw [hab, Subring.coe_mul, norm_mul]
  have hp := norm_pos_iff.2 h0
  have := hc.2
  have hb := norm_nonneg (b : C)
  nlinarith

theorem isDVR : IsDiscreteValuationRing (ints F) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, irreducible_unif h0 h1 hπ, fun {x} hx => ?_⟩
  have hx0 : 0 < ‖(x : C)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx0 h1
  have key : ∀ N : ℕ, ∀ x : ints F, ‖(π : C)‖ ^ N < ‖(x : C)‖ → ∃ n, Associated (π ^ n) x := by
    intro N
    induction N with
    | zero => intro x hx; exact absurd (mem_ints.1 x.2).2 (by simpa using hx)
    | succ N ih =>
      intro x hx
      by_cases hu : IsUnit x
      · exact ⟨0, by rw [pow_zero]; exact associated_one_iff_isUnit.2 hu |>.symm⟩
      · obtain ⟨z, rfl⟩ := dvd_iff.2 (hπ x (mem_ints.1 x.2).1 (not_isUnit_iff.1 hu))
        rw [Subring.coe_mul, norm_mul, pow_succ'] at hx
        obtain ⟨n, hn⟩ := ih z (lt_of_mul_lt_mul_left hx (norm_nonneg _))
        exact ⟨n + 1, by rw [pow_succ']; exact hn.mul_left π⟩
  exact key N x hN

theorem mem_pow_iff [IsDiscreteValuationRing (ints F)] (n : ℕ) (x : ints F) :
    x ∈ IsLocalRing.maximalIdeal (ints F) ^ n ↔ ‖(x : C)‖ ≤ ‖(π : C)‖ ^ n := by
  rw [(irreducible_unif h0 h1 hπ).maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, dvd_iff, SubmonoidClass.coe_pow, norm_pow]

theorem isAdic [IsDiscreteValuationRing (ints F)] : IsAdic (IsLocalRing.maximalIdeal (ints F)) := by
  have hs : ∀ n : ℕ, ((IsLocalRing.maximalIdeal (ints F) ^ n : Ideal (ints F)) : Set (ints F)) =
      Metric.closedBall 0 (‖(π : C)‖ ^ n) := fun n => by
    ext x
    rw [SetLike.mem_coe, mem_pow_iff h0 h1 hπ, mem_closedBall_zero_iff]
    rfl
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs' => ?_⟩
  · rw [hs]
    exact IsUltrametricDist.isOpen_closedBall _ (pow_pos (norm_pos_iff.2 h0) n).ne'
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hs'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    exact ⟨n, by rw [hs]; exact (Metric.closedBall_subset_ball hn).trans h⟩

omit h0 h1 hπ

theorem isAlgClosed_res [IsAlgClosed C] [IsLocalRing (ints F)]
    (hF : ∀ x : C, ‖x‖ ≤ 1 → ∃ y ∈ F, ‖x - y‖ < 1) :
    IsAlgClosed (IsLocalRing.ResidueField (ints F)) := by
  first
  | (rename_i h_1 h_2 h_4 h_5; revert C h_1 h_2 F h_4 h_5 hF; exact @_root_.GlobalTheory.NormEvalSubBound.main_theorem)
  | exact @_root_.GlobalTheory.NormEvalSubBound.main_theorem
  | exact _root_.GlobalTheory.NormEvalSubBound.main_theorem
  | (apply _root_.GlobalTheory.NormEvalSubBound.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormEvalSubBound.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormEvalSubBound.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormEvalSubBound.main_theorem ..)

theorem coe_ints_closure :
    (ints F.topologicalClosure : Set C) = closure {x | x ∈ F ∧ ‖x‖ ≤ 1} := by
  have hc : IsClopen (Metric.closedBall (0 : C) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : {x | x ∈ F ∧ ‖x‖ ≤ 1} = (F : Set C) ∩ Metric.closedBall (0 : C) 1 := by
    ext x; simp
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    exact hc.isOpen.closure_inter ⟨(mem_ints.1 hx).1, by simpa using (mem_ints.1 hx).2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_ints.2 ⟨this.1, by simpa using this.2⟩

end General

variable {l : ℕ} [Fact l.Prime]

open Loc

theorem exists_pow_norm (LL : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 → ∃ n : ℤ, ‖y‖ ^ d = (l : ℝ) ^ n := by
  haveI := LL.2
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] ↥LL.1
  have hLL : IntermediateField.adjoin ℚ_[l] {(α : Om l)} = LL.1 := by
    have := congrArg (IntermediateField.map LL.1.val) hα
    rw [IntermediateField.adjoin_map, Set.image_singleton] at this
    rw [show (α : Om l) = LL.1.val α from rfl, this]
    ext x
    simp
  let E : IntermediateField ↥(MaximalUnramifiedExtension l) (Om l) := IntermediateField.adjoin ↥(MaximalUnramifiedExtension l) {(α : Om l)}
  have hE : E.restrictScalars ℚ_[l] = LL.1 ⊔ MaximalUnramifiedExtension l := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hLL, sup_comm]
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  refine ⟨Module.finrank ↥(MaximalUnramifiedExtension l) ↥E, Module.finrank_pos, fun y hy hy0 => ?_⟩
  rw [← hE] at hy
  let y' : ↥E := ⟨y, hy⟩
  have h := Algebra.norm_eq_prod_embeddings ↥(MaximalUnramifiedExtension l) (Om l) y'
  have hn : ∀ σ : ↥E →ₐ[↥(MaximalUnramifiedExtension l)] Om l, ‖σ y'‖ = ‖y‖ := fun σ => by
    have h1 := minpoly.algHom_eq (σ.restrictScalars ℚ_[l]) σ.injective y'
    have h2 := minpoly.algHom_eq (E.val.restrictScalars ℚ_[l]) E.val.injective y'
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    exact congrArg spectralValue (h1.trans h2.symm)
  have h3 := congrArg norm h
  rw [norm_prod, Finset.prod_congr rfl fun σ _ => hn σ, Finset.prod_const, Finset.card_univ,
    AlgHom.card] at h3
  rw [← h3]
  refine GlobalTheory.UnramValue.norm_of_mem_Kur (Algebra.norm ↥(MaximalUnramifiedExtension l) y').2 ?_
  rw [← norm_ne_zero_iff]
  change ‖algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (Algebra.norm ↥(MaximalUnramifiedExtension l) y')‖ ≠ 0
  rw [h3]
  exact pow_ne_zero _ (norm_ne_zero_iff.2 hy0)

theorem exists_unif (LL : FinExt l) :
    ∃ π ∈ LL.1 ⊔ MaximalUnramifiedExtension l, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := by
  classical
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨d, hd, H⟩ := exists_pow_norm LL
  have key : ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 → ‖y‖ < 1 → ∃ k : ℕ, ‖y‖ ^ d = ((l : ℝ)⁻¹) ^ k := by
    intro y hy h0 h1
    obtain ⟨n, hn⟩ := H y hy h0
    have h2 : (l : ℝ) ^ n < 1 := by rw [← hn]; exact pow_lt_one₀ (norm_nonneg _) h1 hd.ne'
    rw [zpow_lt_one_iff_right₀ hl1] at h2
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat h2.le
    exact ⟨k, by rw [hn, zpow_neg, zpow_natCast, inv_pow]⟩
  have hex : ∃ k : ℕ, ∃ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, y ≠ 0 ∧ ‖y‖ < 1 ∧ ‖y‖ ^ d = ((l : ℝ)⁻¹) ^ k :=
    ⟨d, l, natCast_mem _ _, Nat.cast_ne_zero.2 hp.ne_zero, by
      rw [GlobalTheory.UnramValue.norm_l]; exact inv_lt_one_of_one_lt₀ hl1, by rw [GlobalTheory.UnramValue.norm_l]⟩
  obtain ⟨π, hπ, h0, h1, e⟩ := Nat.find_spec hex
  refine ⟨π, hπ, h0, h1, fun y hy hy1 => ?_⟩
  by_cases hy0 : y = 0
  · simp [hy0]
  obtain ⟨k, hk⟩ := key y hy hy0 hy1
  have hle : Nat.find hex ≤ k := Nat.find_min' hex ⟨y, hy, hy0, hy1, hk⟩
  refine le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) ?_
  rw [hk, e]
  exact pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl1).le hle

def img (LL : FinExt l) : Subfield ℂ_[l] :=
  (LL.1 ⊔ MaximalUnramifiedExtension l).toSubfield.map (algebraMap (Om l) ℂ_[l])

theorem mem_img {LL : FinExt l} {x : ℂ_[l]} :
    x ∈ img LL ↔ ∃ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, (y : ℂ_[l]) = x := Iff.rfl

theorem exists_integers_completion : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (O : Subring ℂ_[l]) (_ : IsDiscreteValuationRing ↥O), (∀ x : ↥(Loc.OL LL), (((x : ↥LL.1) : Loc.Om l) : ℂ_[l]) ∈ O) ∧ (∀ x ∈ O, ‖x‖ ≤ 1) ∧ (∀ x ∈ O, ∀ y ∈ O, ‖x‖ ≤ ‖y‖ → x / y ∈ O) ∧ IsAlgClosed (IsLocalRing.ResidueField ↥O) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥O) ↥O ∧ IsAdic (IsLocalRing.maximalIdeal ↥O) ∧ (O : Set ℂ_[l]) = closure ((fun y : Loc.Om l => (y : ℂ_[l])) '' {y | y ∈ LL.1 ⊔ Loc.MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}) := by
  intro l _ LL
  let F : Subfield ℂ_[l] := (img LL).topologicalClosure
  have hle : ∀ y ∈ LL.1 ⊔ MaximalUnramifiedExtension l, (y : ℂ_[l]) ∈ F := fun y hy =>
    (img LL).le_topologicalClosure (mem_img.2 ⟨y, hy, rfl⟩)
  obtain ⟨π, hπ, h0, h1, hmax⟩ := exists_unif LL
  have h1' : ‖(π : ℂ_[l])‖ < 1 := by rwa [PadicComplex.norm_extends]
  let π' : ints F := ⟨π, mem_ints.2 ⟨hle π hπ, h1'.le⟩⟩
  have h0' : (π' : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff]
    change ‖(π : ℂ_[l])‖ ≠ 0
    rwa [PadicComplex.norm_extends, norm_ne_zero_iff]
  have hmax' : ∀ y ∈ F, ‖y‖ < 1 → ‖y‖ ≤ ‖(π' : ℂ_[l])‖ := by
    intro y hy hy1
    have hc : IsClosed {y : ℂ_[l] | ‖y‖ ≤ ‖(π : ℂ_[l])‖ ∨ 1 ≤ ‖y‖} :=
      (isClosed_le continuous_norm continuous_const).union
        (isClosed_le continuous_const continuous_norm)
    have := closure_minimal (s := (img LL : Set ℂ_[l])) (by
      rintro _ ⟨z, hz, rfl⟩
      change ‖(z : ℂ_[l])‖ ≤ ‖(π : ℂ_[l])‖ ∨ 1 ≤ ‖(z : ℂ_[l])‖
      simp only [PadicComplex.norm_extends]
      rcases lt_or_ge ‖z‖ 1 with h | h
      · exact Or.inl (hmax z hz h)
      · exact Or.inr h) hc hy
    exact this.resolve_right (not_le.2 hy1)
  haveI hdvr : IsDiscreteValuationRing (ints F) := isDVR (π := π') h0' h1' hmax'
  have had := isAdic (π := π') h0' h1' hmax'
  refine ⟨ints F, hdvr, fun x => mem_ints.2 ⟨hle _ (le_sup_left (a := LL.1) x.1.2), ?_⟩,
    fun x hx => (mem_ints.1 hx).2,
    fun x hx y hy h => div_mem_ints (mem_ints.1 hx).1 (mem_ints.1 hy).1 h,
    isAlgClosed_res fun x hx => ?_, ?_, had, ?_⟩
  · rw [PadicComplex.norm_extends]
    have hint : IsIntegral ℤ_[l] ((x : ↥LL.1) : Om l) :=
      (show IsIntegral ℤ_[l] (x : ↥LL.1) from x.2).map (LL.1.val.restrictScalars ℤ_[l])
    obtain ⟨q, hq, hx⟩ := hint
    exact norm_le_one_of_root _ (fun r => by
      rw [GlobalTheory.UnramValue.norm_algebraMap_int]; exact r.norm_le_one) hq hx
  · rcases hx.lt_or_eq with h | h
    · exact ⟨0, zero_mem _, by simpa using h⟩
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hy1 : ‖y‖ = 1 := by
      have e : (y : ℂ_[l]) = x + -(x - y) := by ring
      rw [← PadicComplex.norm_extends, e,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, h]; exact hy.ne'),
        norm_neg, h, max_eq_left hy.le]
    obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := GlobalTheory.MemLoc.FrobLaws.exists_root y hy1
    have hK : ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩
    refine ⟨ζ, hle ζ (le_sup_right (a := LL.1) hK), ?_⟩
    have e : x - (ζ : ℂ_[l]) = (x - y) + ((y - ζ : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hy ?_)
    rwa [PadicComplex.norm_extends]
  · refine had.isAdicComplete_iff.2 ⟨?_, inferInstance⟩
    have : IsClosed (ints F : Set ℂ_[l]) := by rw [coe_ints_closure]; exact isClosed_closure
    exact this.completeSpace_coe
  · rw [coe_ints_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨mem_img.2 ⟨y, hy, rfl⟩, by simpa using h⟩

end GlobalTheory.BigInt
