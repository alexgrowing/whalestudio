import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in

def horCycle (P : Ideal (MRing ι)) (s : MRing ι) : Ideal (MRing ι) →₀ ℕ :=
  (divCycle P s).filter IsHorizontal

open Classical in

def vertCycle (P : Ideal (MRing ι)) (s : MRing ι) : Ideal (MRing ι) →₀ ℕ :=
  (divCycle P s).filter fun W => ¬ IsHorizontal W

def IsClosedPt (Q : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime Q ∧ ringKrullDim (MRing ι ⧸ Q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)

def HasRAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    I P (n + 1) (Fin.snoc L A) = recR I P L A s

end Objects

section TheoremI

def ThmIExists.Statement : Prop := ExistsStatement

def ThmIUnique.Statement : Prop := UniqueStatement

def ThmISymm.Statement : Prop := SymmStatement

def ThmIMultilin.Statement : Prop := MultilinStatement

def SpecIntHeightFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s =
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s - arInt P s A (Fin.elim0 : Fin 0 → HermLine ι)

def RegularityIndependence.Statement : Prop := DimensionOneRationalSectionIndependence

def RegularityAdditive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A B : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSmoothHerm B → IsSectionOn P A s → IsSectionOn P B t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) (A.tensor B) (s * t) =
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s + recR I P (Fin.elim0 : Fin 0 → HermLine ι) B t

def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    HasRAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm A' →
    IsSectionOn P A s → IsSectionOn P A' s' → (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    recR I P (Fin.snoc L A') A s = recR I P (Fin.snoc L A) A' s'

def Choice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a : K → ℤ) (m : ℕ) (Y x : Fin m → Ideal (MRing ι)),
    IsArithVar P d → (∀ i, IsMultiProjPrime (Y i) ∧ P ≤ Y i ∧ Y i ≤ x i ∧ IsClosedPt (x i)) →
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∃ (b : K → ℕ) (s : MRing ι), (∀ l, (b l : ℤ) = a l + k) ∧ IsMultiHomog s b ∧ ∀ i, s ∉ x i) ∧
      ∃ t : MRing ι, IsMultiHomog t (fun _ => k) ∧ ∀ i, t ∉ x i

end TheoremI

section Consequences

def ArithmeticIntersectionSecond.Statement : Prop := MetricChangeStatement

def InductiveIntersectionFormula.Statement : Prop := VerticalStatement

def ArithmeticIntersectionFifth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι),
      IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s →
      I P 1 ![A] = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s - arInt P s A (Fin.elim0 : Fin 0 → HermLine ι)

def Conservation.Statement : Prop := ConservationStatement

def RatR.Statement : Prop := RatRStatement

end Consequences

section PF

def PushforwardProjectivePoint.Statement : Prop := ContractStatement

def PushforwardArithIntersection.Statement : Prop := GenDegStatement

def PushforwardProjLineRankTwo.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (k₀ : FibreBlock κ)
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : HermLine ι'),
      IsBlockMap κ v → IsArithVar P' (d + 1) → IsArithVar (imageZ v P') d → (∀ k, k = k₀) →
      (∃ S : Set (MRingOver G.Φ (fibreIdx ι' κ)),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal κ G = Ideal.span S) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm N →
      I K' ι' P' (d + 1) (Fin.append L' ![N]) = (N.a k₀.1 : ℝ) * I K ι (imageZ v P') d L

def PushforwardProjLineFlag.Statement : Prop := PFStatement

end PF

section Inhabitants

theorem isArithVar_specZ : IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 1 ()) = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl

theorem isMultiHomog_Xc (n : ℕ) (i : Fin n) : IsMultiHomog (Xc n i) (fun _ => 1) := by
  intro m hm k
  obtain ⟨⟩ := k
  have hm' : m ∈ (X (⟨(), i⟩ : (_ : Unit) × Fin n) : MRing (PBlk n)).support := hm
  rw [support_X, Finset.mem_singleton] at hm'
  subst hm'
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (sigma_mk_injective h).symm
  · simp

theorem isSectionOn_Xc (n : ℕ) (i : Fin n) : IsSectionOn ⊥ (fsLine n) (Xc n i) :=
  ⟨fun _ => 1, fun _ => rfl, isMultiHomog_Xc n i, by
    rw [Submodule.mem_bot]
    exact X_ne_zero _⟩

theorem R1.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧ IsSmoothHerm (fsLine 1) ∧
      IsSectionOn ⊥ (fsLine 1) (Xc 1 0) :=
  ⟨isArithVar_specZ, isSmoothHerm_fsLine 1, isSectionOn_Xc 1 0⟩

theorem divSupp_X_disjoint :
    ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) := by
  intro W h0 h1
  have m0 : Xc 2 0 ∈ W := h0.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have m1 : Xc 2 1 ∈ W := h1.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨i, hi⟩ := h0.2 ()
  fin_cases i
  exacts [hi m0, hi m1]

theorem Swap.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 2) ∧ IsSmoothHerm (fsLine 2) ∧
      IsSectionOn ⊥ (fsLine 2) (Xc 2 0) ∧ IsSectionOn ⊥ (fsLine 2) (Xc 2 1) ∧
      ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) :=
  ⟨isArithVar_projLine, isSmoothHerm_fsLine 2, isSectionOn_Xc 2 0, isSectionOn_Xc 2 1, divSupp_X_disjoint⟩

def ptTwo : Ideal (MRing (PBlk 2)) := Ideal.span {C 2, Xc 2 1}

abbrev redTwo : MRing (PBlk 2) →+* MvPolynomial ((_ : Unit) × Fin 2) (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

theorem redTwo_surjective : Function.Surjective redTwo :=
  MvPolynomial.map_surjective _ (ZMod.intCast_surjective)

theorem ptTwo_eq_comap :
    ptTwo = (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2))).comap redTwo := by
  have h1 : inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)) =
      Ideal.map redTwo (Ideal.span {Xc 2 1}) := by
    rw [inhV_singleton, Ideal.map_span, Set.image_singleton]
    simp [Xc]
  rw [h1, Ideal.comap_map_of_surjective _ redTwo_surjective, ← RingHom.ker_eq_comap_bot,
    MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, ptTwo,
    Ideal.span_insert, sup_comm]
  simp

theorem isClosedPt_two : IsClosedPt ptTwo := by
  have hprime : ptTwo.IsPrime := by
    rw [ptTwo_eq_comap]
    exact Ideal.comap_isPrime _ _
  refine ⟨⟨hprime, ⟨{C 2, Xc 2 1}, ?_, rfl⟩, fun _ => ⟨0, ?_⟩⟩, ?_⟩
  · rintro f (rfl | rfl)
    · refine ⟨fun _ => 0, fun m hm k => ?_⟩
      rw [mem_support_iff, coeff_C] at hm
      split_ifs at hm with h
      · subst h
        simp
      · exact absurd rfl hm
    · exact ⟨_, isMultiHomog_Xc 2 1⟩
  · rw [ptTwo_eq_comap, Ideal.mem_comap]
    have : redTwo (X ⟨(), 0⟩) = X ⟨(), 0⟩ := map_X _ _
    rw [this]
    exact inhV_X_nmem (ZMod 2) _ (by decide)
  · have hsurj : Function.Surjective
        ((Ideal.Quotient.mk (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)))).comp redTwo) :=
      Ideal.Quotient.mk_surjective.comp redTwo_surjective
    have hker : RingHom.ker
        ((Ideal.Quotient.mk (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)))).comp redTwo) =
        ptTwo := by
      rw [ptTwo_eq_comap, ← RingHom.comap_ker, Ideal.mk_ker]
    rw [← hker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj), inhV_dim]
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
    rfl

theorem Choice.hyps_inhabited :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧
      ∀ i : Fin 1, IsMultiProjPrime ((fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i) ∧
        ⊥ ≤ (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ∧
        (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ≤ (fun _ => ptTwo) i ∧
        IsClosedPt ((fun _ => ptTwo : Fin 1 → Ideal (MRing (PBlk 2))) i) :=
  ⟨isArithVar_projLine, fun _ => ⟨isArithVar_projLine.2.1, le_rfl, bot_le, isClosedPt_two⟩⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
