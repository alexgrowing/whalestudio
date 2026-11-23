import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentativesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypeRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem h_add_left (a b y : S.V) : S.h (a + b) y = S.h a y + S.h b y := by
  simp only [Frames.h, hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem h_add_right (a y z : S.V) : S.h a (y + z) = S.h a y + S.h a z := by
  simp only [Frames.h, hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem h_smul_left (c : E) (a y : S.V) : S.h (c • a) y = c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem h_smul_right (c : E) (a y : S.V) : S.h a (c • y) = L.cj c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem h_zero_left' (y : S.V) : S.h 0 y = 0 := by
  simp [Frames.h, hf]

private theorem h_zero_right_flag_measures (a : S.V) : S.h a 0 = 0 := by
  simp [Frames.h, hf]

private theorem h_eq_zero_of_span_orth {s t : Set S.V} (hst : ∀ a ∈ s, ∀ b ∈ t, S.h a b = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E s) (hy : y ∈ Submodule.span E t) : S.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hst a ha b hb
    | zero => exact h_zero_right_flag_measures S a
    | add u v _ _ hu hv => rw [h_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [h_smul_right, hu, mul_zero]
  | zero => exact h_zero_left' S y
  | add u v _ _ hu hv => rw [h_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [h_smul_left, hu, mul_zero]

theorem iso_of (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {x y : S.V} (hx : x ∈ S.spanTo g r) (hy : y ∈ S.spanTo g r) : S.h x y = 0 := by
  unfold Frames.spanTo at hx hy
  refine h_eq_zero_of_span_orth S ?_ hx hy
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  change hf L S.Hm (g i) (g j) = 0
  rw [hg, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

theorem spanTo_mono (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)

theorem disj (hli : LinearIndependent E (Sum.elim S.f S.f')) :
    Disjoint (S.spanTo S.f (r + 1)) (S.spanTo S.f' (r + 1)) := by
  have h := (linearIndependent_sum.1 hli).2.2
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  unfold Frames.spanTo
  exact h.mono (Submodule.span_mono (Set.image_subset_range _ _))
    (Submodule.span_mono (Set.image_subset_range _ _))

theorem frame_split (Λ : Submodule L.O S.V) (g g' : Fin (r + 1) → S.V) (h0 : S.th ≠ 0)
    (hg : ∀ b, g b ∈ S.spanTo S.f (r + 1))
    (hg' : ∀ b, g' b ∈ Λ ∧ g' b ∈ S.spanTo S.f' (r + 1)) {m : S.V} (hm : m ∈ S.Mof g g') :
    ∃ a ∈ S.spanTo S.f (r + 1), ∃ a' ∈ S.spanTo S.f' (r + 1), a' ∈ Λ ∧
      algebraMap F E S.th • m = a + a' := by
  have hinv : ∀ v : S.V, algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
    intro v
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨algebraMap F E S.th • g b, Submodule.smul_mem _ _ (hg b), 0, Submodule.zero_mem _,
        Submodule.zero_mem _, by rw [add_zero]⟩
    · refine ⟨-g b, Submodule.neg_mem _ (hg b), g' b, (hg' b).2, (hg' b).1, ?_⟩
      dsimp only
      rw [hinv]
      abel
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    obtain ⟨b, hb, b', hb', hΛ', he'⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb',
      Submodule.add_mem _ hΛ hΛ', by rw [smul_add, he, he']; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    refine ⟨(c : E) • a, Submodule.smul_mem _ _ ha, (c : E) • a', Submodule.smul_mem _ _ ha',
      Λ.smul_mem c hΛ, ?_⟩
    rw [Subring.smul_def, smul_comm, he, smul_add]

private theorem algebraMap_mem_O_of_mem_valuationInteger (L : LocE F E) {x : F} (hx : x ∈ 𝒪[F]) : algebraMap F E x ∈ L.O := by
  rw [L.O_def]
  have := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨x, hx⟩)
  convert this using 1
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rfl

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB B₀ hB₀ hrep hpair
  obtain ⟨hli, -, -, -, -, h0, hthF, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hSD, -, hMsat, hfr, hfr', -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT).2.1
  have hthO : algebraMap F E S.th ∈ L.O := algebraMap_mem_O_of_mem_valuationInteger L hthF
  have hcj : L.cj (algebraMap F E S.th) = algebraMap F E S.th := L.cj.commutes S.th
  have hinv : ∀ v : S.V, algebraMap F E S.th⁻¹ • algebraMap F E S.th • v = v := by
    intro v
    rw [smul_smul, ← map_mul, inv_mul_cancel₀ h0, map_one, one_smul]
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, S.h v w ∈ L.O := fun v hv w hw => (hSD.2 w).2 hw v hv
  have hXX : ∀ v ∈ S.X, ∀ w ∈ S.X, S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f (-algebraMap F E S.T) S.gram hv hw
  have hXX' : ∀ v ∈ S.X', ∀ w ∈ S.X', S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f' (-algebraMap F E S.T') S.gram' hv hw
  have hXME : S.X ≤ S.ME := (spanTo_mono S S.f).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME := (spanTo_mono S S.f').trans le_sup_right
  have hsatΛ : S.sat Λ ≤ Λ := inf_le_left
  have hg : ∀ b, S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    ((hfr (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))).2
  have hg' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (hfr' (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))
  have hdisj := Submodule.disjoint_def.1 (disj S hli)
  have key : ∀ x ∈ S.X, ∀ x' ∈ S.X', S.InTh Λ (x + x') → ∃ u ∈ S.X, ∃ u' ∈ S.X',
      u + u' ∈ B₀ ∧ u + u' ∈ Λ ∧ x' - algebraMap F E S.th • u' ∈ Λ ∧
      ∃ m ∈ Λ, (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • m := by
    rintro x hx x' hx' ⟨y, hyΛ, hxy⟩
    have hyME : y ∈ S.ME := by
      rw [← hinv y, ← hxy]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hXME hx) (hX'ME hx'))
    have hysat : y ∈ S.sat Λ := Submodule.mem_inf.2 ⟨hyΛ, hyME⟩
    obtain ⟨y₀, hy₀, hmM⟩ := hrep y hysat
    obtain ⟨hy₀Λ, hy₀X⟩ := hB₀ y₀ hy₀
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy₀X
    have hmΛ : y - (u + u') ∈ Λ := hsatΛ (hMsat hmM)
    obtain ⟨b, hb, b', hb', hb'Λ, hbb⟩ := frame_split S Λ _ _ h0 hg hg' hmM
    have hsum : (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • (y - (u + u')) := by
      rw [smul_sub, ← hxy, smul_add]
      abel
    have hdiff : b' - (x' - algebraMap F E S.th • u') = 0 := by
      apply hdisj
      · have he : b' - (x' - algebraMap F E S.th • u') = (x - algebraMap F E S.th • u) - b := by
          have h2 := hsum.trans hbb
          linear_combination -h2
        rw [he]
        exact Submodule.sub_mem _
          (spanTo_mono S S.f (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu))) hb
      · exact Submodule.sub_mem _ hb'
          (spanTo_mono S S.f' (Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ hu')))
    have ha' : x' - algebraMap F E S.th • u' = b' := (sub_eq_zero.1 hdiff).symm
    exact ⟨u, hu, u', hu', hy₀, hy₀Λ, by rw [ha']; exact hb'Λ, y - (u + u'), hmΛ, hsum⟩
  refine ⟨hB, ?_, ?_⟩
  · intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
    exact (hlev y hy r).2 ⟨y₀, (hB₀ y₀ hy₀).2, hm⟩
  · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2
    obtain ⟨u₁, hu₁, u₁', hu₁', hB1, hy1, ha1', m₁, hm₁, he1⟩ := key x₁ hx₁ x₁' hx₁' h1
    obtain ⟨u₂, hu₂, u₂', hu₂', hB2, hy2, ha2', m₂, hm₂, he2⟩ := key x₂ hx₂ x₂' hx₂' h2
    generalize ht : algebraMap F E S.th = t at *
    set a₁ := x₁ - t • u₁ with ha₁
    set a₁' := x₁' - t • u₁' with ha₁d
    set a₂' := x₂' - t • u₂' with ha₂d
    have ha₁X : a₁ ∈ S.X := Submodule.sub_mem _ hx₁ (Submodule.smul_mem _ _ hu₁)
    have ha₁'X : a₁' ∈ S.X' := Submodule.sub_mem _ hx₁' (Submodule.smul_mem _ _ hu₁')
    have ha₂'X : a₂' ∈ S.X' := Submodule.sub_mem _ hx₂' (Submodule.smul_mem _ _ hu₂')
    have hB1' : algebraMap F E S.th⁻¹ • (t • u₁ + t • u₁') ∈ B₀ := by rw [← smul_add, hinv]; exact hB1
    have hB2' : algebraMap F E S.th⁻¹ • (t • u₂ + t • u₂') ∈ B₀ := by rw [← smul_add, hinv]; exact hB2
    obtain ⟨c₀, hc₀, hc₀e⟩ := hpair (t • u₁) (Submodule.smul_mem _ _ hu₁) (t • u₁')
      (Submodule.smul_mem _ _ hu₁') (t • u₂) (Submodule.smul_mem _ _ hu₂) (t • u₂')
      (Submodule.smul_mem _ _ hu₂') hB1' hB2'
    have ex₁ : x₁ = t • u₁ + a₁ := by rw [ha₁]; abel
    have ex₂' : x₂' = t • u₂' + a₂' := by rw [ha₂d]; abel
    have eA : S.h x₁ x₂' = S.h (t • u₁) (t • u₂') + S.h (t • u₁) a₂' + S.h a₁ (t • u₂') +
        S.h a₁ a₂' := by
      rw [ex₁, ex₂', h_add_left, h_add_right, h_add_right]
      ring
    have eB : S.h (t • u₁) a₂' = t * S.h u₁ a₂' := h_smul_left S _ _ _
    have eC : S.h (u₁ + u₁') a₂' = S.h u₁ a₂' + S.h u₁' a₂' := h_add_left S _ _ _
    have eD : S.h u₁' a₂' = 0 := hXX' _ hu₁' _ ha₂'X
    have eE : S.h a₁ (t • u₂') = t * S.h a₁ u₂' := by rw [h_smul_right, hcj]
    have eF : S.h a₁ (u₂ + u₂') = S.h a₁ u₂ + S.h a₁ u₂' := h_add_right S _ _ _
    have eG : S.h a₁ u₂ = 0 := hXX _ ha₁X _ hu₂
    have eH : S.h (a₁ + a₁') a₂' = S.h a₁ a₂' + S.h a₁' a₂' := h_add_left S _ _ _
    have eI : S.h (t • m₁) a₂' = t * S.h m₁ a₂' := h_smul_left S _ _ _
    have eJ : S.h a₁' a₂' = 0 := hXX' _ ha₁'X _ ha₂'X
    have eK : S.h (t • m₁) (u₂ + u₂') = t * S.h m₁ (u₂ + u₂') := h_smul_left S _ _ _
    have eL : S.h (a₁ + a₁') (u₂ + u₂') = S.h a₁ (u₂ + u₂') + S.h a₁' (u₂ + u₂') :=
      h_add_left S _ _ _
    rw [he1] at eH eL
    have hO1 : S.h (u₁ + u₁') a₂' ∈ L.O := hint _ hy1 _ ha2'
    have hO2 : S.h m₁ (u₂ + u₂') ∈ L.O := hint _ hm₁ _ hy2
    have hO3 : S.h a₁' (u₂ + u₂') ∈ L.O := hint _ ha1' _ hy2
    have hO4 : S.h m₁ a₂' ∈ L.O := hint _ hm₁ _ ha2'
    refine ⟨c₀ + S.h (u₁ + u₁') a₂' + (t * S.h m₁ (u₂ + u₂') - S.h a₁' (u₂ + u₂')) + S.h m₁ a₂',
      ?_, ?_⟩
    · exact L.O.add_mem (L.O.add_mem (L.O.add_mem hc₀ hO1)
        (L.O.sub_mem (L.O.mul_mem hthO hO2) hO3)) hO4
    · rw [eA, hc₀e]
      linear_combination eB - t * eC - t * eD + eE - t * eF - t * eG - eH + eI - eJ + t * eK - t * eL

end GlobalTheory.HL.TypeRep
