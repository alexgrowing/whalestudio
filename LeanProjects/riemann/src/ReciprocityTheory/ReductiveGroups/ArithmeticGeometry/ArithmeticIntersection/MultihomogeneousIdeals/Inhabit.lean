import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Points

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq (Σ k, ι k)]
  {F : Type*} [Field F]

theorem inh_card {σ : Type*} [Fintype σ] [DecidableEq σ] (S : Finset σ) :
    Nat.card {s // s ∉ S} = Fintype.card σ - S.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]

theorem inh_ptDeg (S : Finset (Σ k, ι k)) (i : ∀ k, ι k)
    (hcov : ∀ s : Σ k, ι k, s ∉ S → s = ⟨s.1, i s.1⟩) (hdisj : ∀ k, (⟨k, i k⟩ : Σ k, ι k) ∉ S) :
    ptDeg (inhV F S) i = 1 := by
  classical
  unfold ptDeg chartIdeal
  apply inh_finrank_quot _ (fun s => if s ∈ S then 0 else 1)
  · apply sup_le
    · rw [Ideal.span_le]
      rintro _ ⟨s, hs, rfl⟩
      simp [RingHom.mem_ker, Finset.mem_coe.mp hs]
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp [RingHom.mem_ker, hdisj k]
  · intro s
    by_cases hs : s ∈ S
    · rw [if_pos hs, map_zero, sub_zero]
      exact Ideal.mem_sup_left (inhV_X_mem F S hs)
    · rw [if_neg hs, map_one, hcov s hs]
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨s.1, rfl⟩)

theorem inh_pointValue {I : IFamily F ι} (hI : IsFieldIntersection I) (S : Finset (Σ k, ι k))
    (i : ∀ k, ι k) (hproj : IsProjVarF (inhV F S) 0)
    (hcov : ∀ s : Σ k, ι k, s ∉ S → s = ⟨s.1, i s.1⟩) (hdisj : ∀ k, (⟨k, i k⟩ : Σ k, ι k) ∉ S)
    (L : Fin 0 → K → ℤ) : I (inhV F S) 0 L = 1 := by
  rw [hI.1 _ L i hproj (fun k => inhV_X_nmem F S (hdisj k)), inh_ptDeg S i hcov hdisj]
  rfl

theorem inh_one_nmem (S : Finset (Σ k, ι k)) : (1 : MRingOver F ι) ∉ inhV F S :=
  fun h => (inhV_isPrime F S).ne_top ((Ideal.eq_top_iff_one _).mpr h)

variable [DecidableEq K]

theorem inh_ratSec_X (V : Ideal (MRingOver F ι)) (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V)
    (hV : (1 : MRingOver F ι) ∉ V) : IsRatSection V (Pi.single p.1 1) (X p) 1 := by
  refine ⟨Pi.single p.1 1, 0, inh_homog_X p, inh_homog_one, hp, hV, fun k => ?_⟩
  by_cases hk : k = p.1
  · subst hk; simp
  · simp [hk]

end Points

theorem inh_single_unit (m : ℕ) : (Pi.single () m : Unit → ℕ) = fun _ => m := by
  funext u; cases u; simp

theorem pointIsVar_thm (F : Type*) [Field F] : PointIsVarStatement F := by
  unfold PointIsVarStatement
  rw [← inhV_empty]
  exact inhV_projVar _ 0 (by decide) (by rw [inh_card]; decide)

theorem lineIsVar_thm (F : Type*) [Field F] : LineIsVarStatement F := by
  unfold LineIsVarStatement
  rw [← inhV_empty]
  exact inhV_projVar _ 1 (by decide) (by rw [inh_card]; decide)

theorem lineSection_thm (F : Type*) [Field F] : LineSectionStatement F := by
  have hQ : (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver F fun _ : Unit => Fin 2)).IsPrime := by
    rw [← inhV_singleton]; infer_instance
  have hrel : IsRelevant (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver F fun _ : Unit => Fin 2)) := by
    rw [← inhV_singleton]; exact inhV_relevant _ (by decide)
  refine ⟨⟨fun _ => 1, 0, ?_, inh_homog_one, ?_, ?_, fun _ => by simp⟩, ?_⟩
  · simpa [inh_single_unit] using inh_homog_X (F := F) (⟨(), 0⟩ : Σ _ : Unit, Fin 2)
  · rw [Ideal.mem_bot]; exact X_ne_zero _
  · rw [Ideal.mem_bot]; exact one_ne_zero
  · rw [ratDiv, inh_divCycle_prime ⊥ _ _ (bot_sup_eq _) hrel, inh_divCycle_one]
    simp

theorem pointDeg_thm (F : Type*) [Field F] : PointDegStatement F := by
  intro I hI
  have h := inh_pointValue hI (∅ : Finset (Σ _ : Unit, Fin 1)) (fun _ => 0)
    (by rw [inhV_empty]; exact pointIsVar_thm F) (by decide) (by decide) Fin.elim0
  rwa [inhV_empty] at h

theorem lineDeg_thm (F : Type*) [Field F] : LineDegStatement F := by
  intro I hI d
  set p : Σ _ : Unit, Fin 2 := ⟨(), 0⟩
  have hQ : (Ideal.span {X p} : Ideal (MRingOver F fun _ : Unit => Fin 2)).IsPrime := by
    rw [← inhV_singleton]; infer_instance
  have hrel : IsRelevant (Ideal.span {X p} : Ideal (MRingOver F fun _ : Unit => Fin 2)) := by
    rw [← inhV_singleton]; exact inhV_relevant _ (by decide)
  have hpt : I (Ideal.span {X p}) 0 Fin.elim0 = 1 := by
    rw [← inhV_singleton]
    exact inh_pointValue hI {p} (fun _ => 1)
      (inhV_projVar _ 0 (by decide) (by rw [inh_card]; decide)) (by decide) (by decide) _
  have hP1 := lineIsVar_thm F
  have hXm : ∀ m : ℕ, (X p ^ m : MRingOver F fun _ : Unit => Fin 2) ∉ (⊥ : Ideal _) := fun m => by
    rw [Ideal.mem_bot]; exact pow_ne_zero _ (X_ne_zero _)
  have h1 : (1 : MRingOver F fun _ : Unit => Fin 2) ∉ (⊥ : Ideal _) := by
    rw [Ideal.mem_bot]; exact one_ne_zero
  have hhom : ∀ m : ℕ, IsMultiHomog (X p ^ m : MRingOver F fun _ : Unit => Fin 2) (fun _ => m) :=
    fun m => by
      have := inh_homog_X_pow (F := F) p m
      rwa [show p.1 = () from rfl, inh_single_unit] at this
  have e : ∀ A : Unit → ℤ, (![A] : Fin 1 → Unit → ℤ) =
      Fin.snoc (α := fun _ => Unit → ℤ) Fin.elim0 A := by
    intro A; funext j; fin_cases j; rfl
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [e, hI.2 ⊥ 0 Fin.elim0 _ (X p ^ m) 1 hP1
      ⟨fun _ => m, 0, hhom m, inh_homog_one, hXm m, h1, fun _ => by simp⟩,
      ratDiv, inh_divCycle_pow (X p) (X_ne_zero _) hrel, inh_divCycle_one]
    simp [inh_cycEval_single, hpt]
  · rw [e, hI.2 ⊥ 0 Fin.elim0 _ 1 (X p ^ m) hP1
      ⟨0, fun _ => m, inh_homog_one, hhom m, h1, hXm m, fun _ => by simp⟩,
      ratDiv, inh_divCycle_pow (X p) (X_ne_zero _) hrel, inh_divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]
    rw [← Finsupp.single_neg, inh_cycEval_single, hpt, mul_one]

theorem quadric_thm (F : Type*) [Field F] : QuadricStatement F := by
  intro I hI
  let σ := Σ _ : Fin 2, Fin 2
  have e : ∀ a b : Fin 2 → ℤ, (![a, b] : Fin 2 → Fin 2 → ℤ) =
      Fin.snoc (α := fun _ => Fin 2 → ℤ) ![a] b := by
    intro a b; funext j; fin_cases j <;> rfl
  have e1 : ∀ a : Fin 2 → ℤ, (![a] : Fin 1 → Fin 2 → ℤ) =
      Fin.snoc (α := fun _ => Fin 2 → ℤ) Fin.elim0 a := by
    intro a; funext j; fin_cases j; rfl
  have hP : IsProjVarF (⊥ : Ideal (MRingOver F fun _ : Fin 2 => Fin 2)) 2 := by
    rw [← inhV_empty]
    exact inhV_projVar _ 2 (by decide) (by rw [inh_card]; decide)
  have hW : ∀ p : σ, p.2 = 0 → IsProjVarF (inhV F ({p} : Finset σ)) 1 := by
    intro p hp
    refine inhV_projVar _ 1 ?_ (by rw [inh_card]; simp)
    intro k; refine ⟨1, ?_⟩
    rw [Finset.mem_singleton]; intro h; rw [← h] at hp; simp at hp
  have hbot : ∀ p : σ, (⊥ : Ideal (MRingOver F fun _ : Fin 2 => Fin 2)) ⊔ Ideal.span {X p} =
      inhV F ({p} : Finset σ) := fun p => by rw [bot_sup_eq, inhV_singleton]
  have hsec : ∀ (S : Finset σ) (p : σ), p ∉ S →
      IsRatSection (inhV F S) (Pi.single p.1 1) (X p) 1 :=
    fun S p hp => inh_ratSec_X _ p (inhV_X_nmem F S hp) (inh_one_nmem S)
  constructor
  ·
    have hpt : I (inhV F ({⟨0, 0⟩, ⟨1, 0⟩} : Finset σ)) 0 Fin.elim0 = 1 :=
      inh_pointValue hI _ (fun _ => 1)
        (inhV_projVar _ 0 (by decide) (by rw [inh_card]; decide)) (by decide) (by decide) _
    have hline : I (inhV F ({⟨1, 0⟩} : Finset σ)) 1 ![Pi.single 0 1] = 1 := by
      rw [e1, hI.2 _ 0 Fin.elim0 _ (X ⟨0, 0⟩) 1 (hW ⟨1, 0⟩ rfl) (hsec _ ⟨0, 0⟩ (by decide)), ratDiv,
        inh_divCycle_prime _ _ (inhV F ({⟨0, 0⟩, ⟨1, 0⟩} : Finset σ)) (inhV_insert F _ _)
          (inhV_relevant _ (by decide)), inh_divCycle_one]
      simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, sub_zero, Nat.cast_one]
      rw [inh_cycEval_single, hpt, one_mul]
    rw [e, hI.2 ⊥ 1 _ _ (X ⟨1, 0⟩) 1 hP (by rw [← inhV_empty]; exact hsec ∅ ⟨1, 0⟩ (by decide)),
      ratDiv, inh_divCycle_prime _ _ _ (hbot _) (inhV_relevant _ (by decide)), inh_divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, sub_zero, Nat.cast_one]
    rw [inh_cycEval_single, hline, one_mul]
  ·

    have hline : I (inhV F ({⟨0, 0⟩} : Finset σ)) 1 ![Pi.single 0 1] = 0 := by
      have hirr : ¬ IsRelevant (inhV F ({⟨0, 1⟩, ⟨0, 0⟩} : Finset σ)) := by
        intro h
        obtain ⟨i, hi⟩ := h 0
        exact hi (inhV_X_mem F _ (by fin_cases i <;> decide))
      rw [e1, hI.2 _ 0 Fin.elim0 _ (X ⟨0, 1⟩) 1 (hW ⟨0, 0⟩ rfl) (hsec _ ⟨0, 1⟩ (by decide)), ratDiv,
        inh_divCycle_irrel _ _ _ (inhV_insert F _ _) hirr, inh_divCycle_one]
      simp [cycEval]
    rw [e, hI.2 ⊥ 1 _ _ (X ⟨0, 0⟩) 1 hP (by rw [← inhV_empty]; exact hsec ∅ ⟨0, 0⟩ (by decide)),
      ratDiv, inh_divCycle_prime _ _ _ (hbot _) (inhV_relevant _ (by decide)), inh_divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, sub_zero, Nat.cast_one]
    rw [inh_cycEval_single, hline, mul_zero]

end ReciprocityTheory.ChartRestriction.G.AI.I1
