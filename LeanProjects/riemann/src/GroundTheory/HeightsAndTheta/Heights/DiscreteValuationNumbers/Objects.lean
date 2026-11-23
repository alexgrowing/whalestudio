import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section Ring

variable {K : Type*} (ι : K → Type*)

abbrev MRing (R : Type*) [CommRing R] : Type _ := MvPolynomial (Σ k, ι k) R

variable [DecidableEq K]

def blockWeight : (Σ k, ι k) → K → ℕ := fun v => Pi.single v.1 1

variable {ι} {R : Type*} [CommRing R]

def IsMultiHomog (f : MRing ι R) (b : K → ℕ) : Prop :=
  IsWeightedHomogeneous (blockWeight ι) f b

def IsMultiHomogIdeal (I : Ideal (MRing ι R)) : Prop :=
  ∀ f ∈ I, ∀ b : K → ℕ, weightedHomogeneousComponent (blockWeight ι) b f ∈ I

def IsRelevant (I : Ideal (MRing ι R)) : Prop :=
  ∀ k, ∃ i : ι k, (X ⟨k, i⟩ : MRing ι R) ∉ I

structure IsMultiProjPrime (P : Ideal (MRing ι R)) : Prop where
  isPrime : P.IsPrime
  multiHomog : IsMultiHomogIdeal P
  relevant : IsRelevant P

end Ring

section Cycles

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

def multAt (J W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι R ⧸ J))

open Classical in

def divCycle (P : Ideal (MRing ι R)) (f : MRing ι R) (W : Ideal (MRing ι R)) : ℤ :=
  if h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W then
    haveI : W.IsPrime := h.1.1.1
    ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ)
  else 0

def ratDiv (P : Ideal (MRing ι R)) (f g : MRing ι R) (W : Ideal (MRing ι R)) : ℤ :=
  divCycle P f W - divCycle P g W

def cycEval (n : Ideal (MRing ι R) → ℤ) (Z : Ideal (MRing ι R) → ℤ) : ℤ :=
  ∑ᶠ W, Z W * n W

end Cycles

section Field

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def gradedPiece (P : Ideal (MRing ι F)) (m : K → ℕ) : Submodule F (MRing ι F ⧸ P) :=
  (weightedHomogeneousSubmodule F (blockWeight ι) m).map (Ideal.Quotient.mkₐ F P).toLinearMap

open Classical in

def hilbFn (P : Ideal (MRing ι F)) (m : K → ℤ) : ℤ :=
  if ∀ k, 0 ≤ m k then (Module.finrank F (gradedPiece P (fun k => (m k).toNat)) : ℤ) else 0

def diffStep (b : K → ℤ) (h : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  fun m => h m - h (m - b)

def mixedDiff {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (List.ofFn bs).foldr diffStep h

open Classical in

def eventualValue (f : (K → ℤ) → ℤ) : ℤ :=
  if h : ∃ c, ∀ᶠ m in Filter.atTop, f m = c then h.choose else 0

def intNum (F : Type*) [Field F] (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  eventualValue (mixedDiff bs (hilbFn P))

end Field

section DVR

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def specialIdeal (W : Ideal (MRing ι O)) : Ideal (MRing ι (IsLocalRing.ResidueField O)) :=
  W.map (MvPolynomial.map (IsLocalRing.residue O))

def genFib (P : Ideal (MRing ι O)) : Ideal (MRing ι (FractionRing O)) :=
  P.map (MvPolynomial.map (algebraMap O (FractionRing O)))

def vNum (W : Ideal (MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  intNum (IsLocalRing.ResidueField O) (specialIdeal W) bs

def gNum (P : Ideal (MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  intNum (FractionRing O) (genFib P) bs

structure IsModelOver [Fintype K] (P : Ideal (MRing ι O)) (d : ℕ) : Prop where
  multiProj : IsMultiProjPrime P
  noTorsion : P.comap (C : O →+* MRing ι O) = ⊥
  dim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

structure IsVerticalDivisor (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) :
    Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  vertical : ∀ W, ratDiv P f g W ≠ 0 → (C ϖ : MRing ι O) ∈ W
  unit_off_special : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

end DVR

section Examples

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem isMultiProjPrime_bot {R : Type*} [CommRing R] [IsDomain R] [∀ k, Nonempty (ι k)] :
    IsMultiProjPrime (⊥ : Ideal (MRing ι R)) where
  isPrime := Ideal.isPrime_bot
  multiHomog := by
    intro f hf b
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  relevant := by
    intro k
    refine ⟨Classical.arbitrary _, ?_⟩
    rw [Ideal.mem_bot]
    exact X_ne_zero _

omit [DecidableEq K] in

theorem divCycle_one {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (W : Ideal (MRing ι R)) :
    divCycle P 1 W = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  have hW : W.IsPrime := h.1.1
  have : P ⊔ Ideal.span {(1 : MRing ι R)} = ⊤ := by
    rw [Ideal.span_singleton_one, sup_top_eq]
  exact hW.ne_top (top_le_iff.mp (this ▸ h.1.2))

theorem isVerticalDivisor_uniformiser {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime]
    (hϖ : (C ϖ : MRing ι O) ∉ H) :
    IsVerticalDivisor H ϖ 0 (C ϖ) 1 where
  degrees := ⟨0, 0, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one _ _, by
    funext k; simp⟩
  num_not_mem := hϖ
  den_not_mem := Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)
  vertical := by
    intro W hW
    unfold ratDiv at hW
    rw [divCycle_one, sub_zero] at hW
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    · exact absurd rfl hW
  unit_off_special := by
    intro W hW _ _ hϖW
    refine ⟨1, C ϖ, ?_, hϖW, ?_⟩
    · exact (Ideal.ne_top_iff_one W).mp hW.ne_top
    · rw [one_mul, mul_one, sub_self]
      exact H.zero_mem

theorem isModelOver_projectiveSpace {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (n : ℕ) :
    IsModelOver (⊥ : Ideal (MRing (fun _ : Unit => Fin (n + 1)) O)) n where
  multiProj := isMultiProjPrime_bot
  noTorsion := by
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot, C_eq_zero]
  dim := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
    have hc : Nat.card ((_ : Unit) × Fin (n + 1)) = n + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    norm_cast
    omega

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
