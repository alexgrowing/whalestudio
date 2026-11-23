import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

noncomputable section

namespace GlobalTheory.FockInclHarm

open MvPolynomial

section Lemmas

variable {P Q R S : ℕ}

theorem incl_injective (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) :
    Function.Injective (Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀)) :=
  Function.Injective.prodMap Function.injective_id (skipIx_injective r₀ s₀)

theorem linePos_incl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (l : Ln P Q R S) :
    linePos (Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀) l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem incl_ne_left (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (a : Ix P Q) (m : Ln P Q R S) :
    Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀) m ≠ (a, Sum.inl r₀) := by
  rcases m with ⟨b, c | c⟩ <;> simp [skipIx, Fin.succAbove_ne]

theorem incl_ne_right (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (a : Ix P Q) (m : Ln P Q R S) :
    Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀) m ≠ (a, Sum.inr s₀) := by
  rcases m with ⟨b, c | c⟩ <;> simp [skipIx, Fin.succAbove_ne]

theorem incl_ne_of_not_mem (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (a : Ix P Q) (c : Ix (R + 1) (S + 1))
    (hc : c ∉ Set.range (skipIx r₀ s₀)) (m : Ln P Q R S) :
    Prod.map (id : Ix P Q → Ix P Q) (skipIx r₀ s₀) m ≠ (a, c) := by
  rcases m with ⟨b, d⟩
  intro h
  simp only [Prod.map, Prod.mk.injEq] at h
  exact hc ⟨d, h.2⟩

theorem pderiv_polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (a : Ix P Q) (c : Ix R S) (g : Pol P Q R S) :
    pderiv ((a, skipIx r₀ s₀ c) : Ln P Q (R + 1) (S + 1)) (polIncl P Q r₀ s₀ g) =
      polIncl P Q r₀ s₀ (pderiv ((a, c) : Ln P Q R S) g) :=
  pderiv_rename (incl_injective r₀ s₀) (a, c) g

theorem omE_polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (l l' : Ln P Q R S) (f : Pol P Q R S) :
    omE (Prod.map id (skipIx r₀ s₀) l) (Prod.map id (skipIx r₀ s₀) l') (polIncl P Q r₀ s₀ f) =
      polIncl P Q r₀ s₀ (omE l l' f) := by
  have := GlobalTheory.FockSplit.omE_rename_mul (Prod.map id (skipIx r₀ s₀)) (incl_injective r₀ s₀)
    (linePos_incl r₀ s₀) l l' f 1 (fun _ => by simp)
  simpa [polIncl] using this

theorem lineSign_eq (a : Ix P Q) (c : Ix R S) :
    lineSign a c = if linePos ((a, c) : Ln P Q R S) then 1 else -1 := by
  rcases a with a | a <;> rcases c with c | c <;> rfl

theorem omE_free (a b : Ix P Q) (c : Ix R S) (hab : sameBlock a b) (g : Pol P Q R S)
    (ha : pderiv ((a, c) : Ln P Q R S) g = 0) (hb : pderiv ((b, c) : Ln P Q R S) g = 0) :
    omE ((a, c) : Ln P Q R S) (b, c) g = if a = b then (lineSign a c / 2) • g else 0 := by
  have hpos : linePos ((a, c) : Ln P Q R S) = linePos ((b, c) : Ln P Q R S) := by
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock, linePos]
  by_cases e : a = b
  · subst e
    rw [if_pos rfl, lineSign_eq]
    simp only [omE, LinearMap.add_apply, Module.End.mul_apply, raiB, lowB, if_true]
    cases hl : linePos ((a, c) : Ln P Q R S)
    · simp [Derivation.leibniz, ha, pderiv_X_self]
      module
    · simp [ha]
  · rw [if_neg e]
    have hne : ((a, c) : Ln P Q R S) ≠ (b, c) := fun h => e (Prod.mk.inj h).1
    simp only [omE, LinearMap.add_apply, Module.End.mul_apply, raiB, lowB, if_neg hne, LinearMap.zero_apply,
      add_zero, ← hpos]
    cases hl : linePos ((a, c) : Ln P Q R S)
    · simp [Derivation.leibniz, ha, pderiv_X_of_ne (Ne.symm hne)]
    · simp [hb]

theorem fockAct1_Eab_polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (a b : Ix P Q) (hab : sameBlock a b)
    (f : Pol P Q R S) :
    fockAct1 P Q (R + 1) (S + 1) (Eab a b) (polIncl P Q r₀ s₀ f) =
      polIncl P Q r₀ s₀ (fockAct1 P Q R S (Eab a b) f) := by
  rw [fockAct1_Eab, fockAct1_Eab, LinearMap.sum_apply, LinearMap.sum_apply, map_sum,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_succAbove _ r₀, Fin.sum_univ_succAbove _ s₀]
  have h1 : ∑ i : Fin R, omE ((a, Sum.inl (r₀.succAbove i)) : Ln P Q (R + 1) (S + 1)) (b, Sum.inl (r₀.succAbove i))
      (polIncl P Q r₀ s₀ f) = ∑ i : Fin R, polIncl P Q r₀ s₀ (omE ((a, Sum.inl i) : Ln P Q R S) (b, Sum.inl i) f) :=
    Finset.sum_congr rfl fun i _ => omE_polIncl r₀ s₀ (a, Sum.inl i) (b, Sum.inl i) f
  have h2 : ∑ i : Fin S, omE ((a, Sum.inr (s₀.succAbove i)) : Ln P Q (R + 1) (S + 1)) (b, Sum.inr (s₀.succAbove i))
      (polIncl P Q r₀ s₀ f) = ∑ i : Fin S, polIncl P Q r₀ s₀ (omE ((a, Sum.inr i) : Ln P Q R S) (b, Sum.inr i) f) :=
    Finset.sum_congr rfl fun i _ => omE_polIncl r₀ s₀ (a, Sum.inr i) (b, Sum.inr i) f
  have hz : ∀ v : Ln P Q (R + 1) (S + 1), (∀ m, Prod.map id (skipIx r₀ s₀) m ≠ v) →
      pderiv v (polIncl P Q r₀ s₀ f) = 0 := fun v hv =>
    GlobalTheory.FockSplit.pderiv_rename_eq_zero _ v hv f
  have key : omE ((a, Sum.inl r₀) : Ln P Q (R + 1) (S + 1)) (b, Sum.inl r₀) (polIncl P Q r₀ s₀ f) +
      omE ((a, Sum.inr s₀) : Ln P Q (R + 1) (S + 1)) (b, Sum.inr s₀) (polIncl P Q r₀ s₀ f) = 0 := by
    rw [omE_free a b _ hab _ (hz _ (incl_ne_left r₀ s₀ a)) (hz _ (incl_ne_left r₀ s₀ b)),
      omE_free a b _ hab _ (hz _ (incl_ne_right r₀ s₀ a)) (hz _ (incl_ne_right r₀ s₀ b))]
    split_ifs
    · rw [← add_smul]
      rcases a with a | a <;> simp [lineSign] <;> norm_num
    · simp
  rw [h1, h2, add_add_add_comm, key, zero_add]

theorem fockAct1_polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) {X : Mat P Q} (hX : IsKC X) (f : Pol P Q R S) :
    fockAct1 P Q (R + 1) (S + 1) X (polIncl P Q r₀ s₀ f) = polIncl P Q r₀ s₀ (fockAct1 P Q R S X f) := by
  have hZ : X = ∑ a, ∑ b, X a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · rw [fockAct1_Eab_polIncl r₀ s₀ a b h]
  · simp [hX a b h]

theorem isPC_submatrix (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) {Z : Mat (R + 1) (S + 1)} (hZ : IsPC Z) :
    IsPC (Z.submatrix (skipIx r₀ s₀) (skipIx r₀ s₀)) := by
  intro c d h
  apply hZ
  rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock, skipIx]

theorem minusPart_polIncl (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) {Z : Mat (R + 1) (S + 1)} (hZ : IsPC Z)
    (f : Pol P Q R S) :
    minusPart (fockAct2 P Q (R + 1) (S + 1) Z) (polIncl P Q r₀ s₀ f) =
      polIncl P Q r₀ s₀ (minusPart (fockAct2 P Q R S (Z.submatrix (skipIx r₀ s₀) (skipIx r₀ s₀))) f) := by
  rw [GlobalTheory.JointHarm.minusPart_fockAct2_offDiagonal hZ, GlobalTheory.JointHarm.minusPart_fockAct2_offDiagonal (isPC_submatrix r₀ s₀ hZ), map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hz : ∀ (v : Ln P Q (R + 1) (S + 1)) (g : Pol P Q R S), (∀ m, Prod.map id (skipIx r₀ s₀) m ≠ v) →
      pderiv v (polIncl P Q r₀ s₀ g) = 0 := fun v g hv =>
    GlobalTheory.FockSplit.pderiv_rename_eq_zero _ v hv g
  have hren : ∀ v : Ln P Q (R + 1) (S + 1), ∃ g, pderiv v (polIncl P Q r₀ s₀ f) = polIncl P Q r₀ s₀ g := by
    rintro ⟨b, d⟩
    by_cases hd : d ∈ Set.range (skipIx r₀ s₀)
    · obtain ⟨d', rfl⟩ := hd
      exact ⟨_, pderiv_polIncl r₀ s₀ b d' f⟩
    · exact ⟨0, by rw [map_zero]; exact hz _ _ (incl_ne_of_not_mem r₀ s₀ b d hd)⟩
  rw [map_sum]
  symm
  refine Fintype.sum_of_injective (M := Pol P Q (R + 1) (S + 1)) (skipIx r₀ s₀) (skipIx_injective r₀ s₀) _ _ ?_ ?_
  · intro c hc
    refine Finset.sum_eq_zero fun d _ => ?_
    split_ifs
    · rfl
    · obtain ⟨g, hg⟩ := hren (a, d)
      rw [hg, hz _ _ (incl_ne_of_not_mem r₀ s₀ a c hc), smul_zero]
  · intro c
    rw [map_sum]
    refine Fintype.sum_of_injective (M := Pol P Q (R + 1) (S + 1)) (skipIx r₀ s₀) (skipIx_injective r₀ s₀) _ _ ?_ ?_
    · intro d hd
      split_ifs
      · rfl
      · rw [hz _ _ (incl_ne_of_not_mem r₀ s₀ a d hd), map_zero, smul_zero]
    · intro d
      have hp : linePos ((a, skipIx r₀ s₀ c) : Ln P Q (R + 1) (S + 1)) = linePos ((a, c) : Ln P Q R S) :=
        linePos_incl r₀ s₀ (a, c)
      rw [hp]
      split_ifs
      · simp
      · rw [map_smul, pderiv_polIncl, pderiv_polIncl]
        rfl

end Lemmas

theorem harmTy_map_polIncl_le : ∀ (P Q R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (x : ℚ),
    (harmTy P Q R S x).map (polIncl P Q r₀ s₀).toLinearMap ≤ harmTy P Q (R + 1) (S + 1) x := by
  intro P Q R S r₀ s₀ x
  rw [harmTy, Submodule.map_span_le]
  rintro f ⟨hf1, hf2⟩
  have hf1' : ∀ Z : Mat R S, IsPC Z → minusPart (fockAct2 P Q R S Z) f = 0 := hf1
  apply Submodule.subset_span
  refine ⟨?_, ?_⟩
  · intro Z hZ
    show minusPart _ (polIncl P Q r₀ s₀ f) = 0
    rw [minusPart_polIncl r₀ s₀ hZ, hf1' _ (isPC_submatrix r₀ s₀ hZ), map_zero]
  · intro X hX
    show fockAct1 P Q (R + 1) (S + 1) X (polIncl P Q r₀ s₀ f) = _ • polIncl P Q r₀ s₀ f
    rw [fockAct1_polIncl r₀ s₀ hX, hf2 X hX, map_smul]

end GlobalTheory.FockInclHarm
