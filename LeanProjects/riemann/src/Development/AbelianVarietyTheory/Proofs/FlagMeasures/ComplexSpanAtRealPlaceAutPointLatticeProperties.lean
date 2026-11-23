import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpSetBaseChange
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiiIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsMore

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.RealSpan

section General

variable {E A : Type} [Field E] [CommRing A] {n : ℕ}

theorem span_image_span (ι : E →+* A) (S : Set (Fin n → E)) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) =
      Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) ''
        (Submodule.span E S : Set (Fin n → E))) := by
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext i; simp
    simp only [this]
    exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => ι ((y + z) i)) = (fun i => ι (y i)) + fun i => ι (z i) := by funext i; simp
    simp only [this]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (fun i => ι ((c • y) i)) = ι c • fun i => ι (y i) := by funext i; simp
    simp only [this]
    exact Submodule.smul_mem _ _ hy

theorem span_image_univ (ι : E →+* A) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem map_mulVec_image (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    Y.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((Y *ᵥ w) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_mem (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S T : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u ∈ T) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' T) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact Submodule.subset_span ⟨Y *ᵥ w, h w hw, (map_mulVec_image ι Y w).symm⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem map_mulVec_eq_zero (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u = 0) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [map_mulVec_image, h w hw]
    funext i; simp
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]

variable (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (hc : ∀ e, s (ι e) = ι (σ e))
  (J : Matrix (Fin n) (Fin n) E)

include hc

theorem isSkew_map (Y : Matrix (Fin n) (Fin n) E) (h : IsSkew σ J Y) :
    IsSkew s (J.map ι) (Y.map ι) := by
  rw [← GlobalTheory.CoverRadiiEq.skew_iff] at h ⊢
  have h1 : Formalism.UG.cT s (Y.map ι) = (Formalism.UG.cT σ Y).map ι := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [h1, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), h]
  simp

theorem inNil_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InNil σ J W Y) :
    InNil s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨isSkew_map σ s ι hc J Y h1, fun u => ?_, fun u hu => ?_, map_mulVec_eq_zero ι Y _ h4⟩
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc]
    exact map_mulVec_mem ι Y Set.univ _ (fun u _ => h2 u) u (by rw [span_image_univ]; trivial)
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
    exact map_mulVec_mem ι Y _ _ h3 u hu

theorem inCen_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InCen σ J W Y) :
    InCen s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  refine ⟨inNil_map σ s ι hc J W Y h.1, fun u hu => ?_⟩
  rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
  exact map_mulVec_eq_zero ι Y _ h.2 u hu

end General

section Lattice

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | (apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main ..)

omit [NumberField E] in
theorem mem_perpSet_span (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (y : Fin n → E) :
    y ∈ perpSet σ J (Submodule.span E S) ↔ ∀ w ∈ S, Formalism.UG.hform σ J w y = 0 := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp [Formalism.UG.hform]
  | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_left, hu, mul_zero]

theorem span_perp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (Λ R : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (Submodule.span E (Submodule.span (𝓞 E) {y | y ∈ Λ ∧ ∀ s ∈ R, Formalism.UG.hform σ J s y = 0} :
      Set (Fin n → E)) : Set (Fin n → E)) = perpSet σ J (Submodule.span E (R : Set (Fin n → E))) := by
  rw [Submodule.span_span_of_tower]
  ext y
  rw [mem_perpSet_span]
  constructor
  · intro hy w hw
    induction hy using Submodule.span_induction with
    | mem u hu => exact hu.2 w hw
    | zero => simp [Formalism.UG.hform]
    | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_right, hu, mul_zero]
  · intro hy
    obtain ⟨c, hc, hcy⟩ := exists_smul_mem Λ y (by rw [hΛ]; trivial)
    have hc1 : algebraMap (𝓞 E) E c ≠ 0 := by simpa using hc
    rw [← algebraMap_smul E c] at hcy
    have : y = (algebraMap (𝓞 E) E c)⁻¹ • algebraMap (𝓞 E) E c • y := by
      rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hcy, fun w hw => ?_⟩)
    rw [Formalism.UG.P.csScale_hform_smul_right, hy w hw, mul_zero]

end Lattice

theorem conj_emb (I : AutInst) (v : InfinitePlace I.F) (e : I.E) :
    starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
  (I.cm.cmUnram.2.1 (I.φ v) e).symm

theorem spanAt_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  intro I x R
  have h1 : ∀ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) v, spanAt I R v = Submodule.span ℂ
      ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) ''
        (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E))) :=
    fun R v => span_image_span (I.φ v) _
  have hΛ := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  refine ⟨h1 R, fun v => ?_, fun v => ?_, fun Y hY v => ?_, fun Y hY v => ?_⟩
  · rw [h1, hΛ]
    exact span_image_univ _
  · rw [h1, h1, GlobalTheory.PerpBaseChange.perpSet_baseChange _ _ (starRingEnd I.E) _ _ _ _ _ (conj_emb I v), perpIn,
      span_perp _ _ _ _ hΛ]
  · rw [h1]
    exact inNil_map _ _ _ (conj_emb I v) _ _ Y hY
  · rw [h1]
    exact inCen_map _ _ _ (conj_emb I v) _ _ Y hY

end GlobalTheory.RealSpan
