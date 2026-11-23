import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem relDim_of_ringKrullDim_eq (I : Ideal (MRing ι F)) (d : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = (d : WithBot ℕ∞)) :
    relDim I = (((d : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  rfl

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem relDim_map_injective :
    Function.Injective (WithBot.map (fun d : ℕ∞ =>
      WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)) :=
  WithBot.map_injective (WithTop.map_injective fun a b h => by
    have h' : (a : ℤ) - Fintype.card K = (b : ℤ) - Fintype.card K := h
    omega)

theorem isMultiProjPrime_relDim_zero_of_divCycle_ne_zero {P : Ideal (MRing ι F)}
    (hP : IsMultiProjPrime P) (hdim : relDim P = 1) {b : K → ℕ} {f : MRing ι F}
    (hf : IsMultiHomog f b) (hfP : f ∉ P) {W : Ideal (MRing ι F)} (hW : divCycle P f W ≠ 0) :
    IsMultiProjPrime W ∧ relDim W = 0 := by
  have h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by rw [divCycle, dif_neg h])
  obtain ⟨hmin, hrel⟩ := h
  have hWh : IsMultiHomogIdeal W := (Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((Bridge.isMultiHomogIdeal_iff P).mp hP.multiHomog) ((Bridge.isMultiHomog_iff f b).mp hf) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.isPrime
  have hPd : ringKrullDim (MRing ι F ⧸ P) = ((Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    apply relDim_map_injective (K := K)
    change relDim P = _
    rw [hdim]
    show (1 : WithBot (WithTop ℤ)) =
      ((((Fintype.card K + 1 : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ))
    have e : (((Fintype.card K + 1 : ℕ) : ℤ) - Fintype.card K : ℤ) = 1 := by push_cast; ring
    rw [e]
    rfl
  have key : ringKrullDim (MRing ι F ⧸ W) + 1 = ringKrullDim (MRing ι F ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hfP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd] at key
  have hWd := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  rw [relDim_of_ringKrullDim_eq W _ hWd, sub_self]
  rfl

end

theorem DivPrincipalDegree.proof (h₁ : CutRational.Statement.{u}) (h₂ : IntNumBase.Statement.{u})
    (h₃ : IntNumZeroSlot.Statement.{u}) : DivPrincipalDegree.Statement.{u} := by
  intro F _ K _ _ ι _ P hP hdim b f g hf hg hfP hgP
  have hcut := h₁ F K ι P hP 0 (by rw [hdim]; rfl) b b f g hf hg hfP hgP ![]
  have hzero : intNum F P (Fin.snoc (α := fun _ => K → ℤ) (![] : Fin 0 → K → ℤ)
      (fun k => (b k : ℤ) - b k)) = 0 :=
    (h₃ F K ι P).1 1 _ (Fin.last 0) (by rw [Fin.snoc_last]; funext k; simp)
  rw [hzero] at hcut
  refine Eq.trans ?_ hcut.symm
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : ratDiv P f g W = 0
  · rw [hW, zero_mul, zero_mul]
  · congr 1
    have hfg : divCycle P f W ≠ 0 ∨ divCycle P g W ≠ 0 := by
      by_contra h
      push Not at h
      exact hW (by rw [ratDiv, h.1, h.2, sub_zero])
    obtain ⟨hWm, hW0⟩ := hfg.elim (isMultiProjPrime_relDim_zero_of_divCycle_ne_zero hP hdim hf hfP)
      (isMultiProjPrime_relDim_zero_of_divCycle_ne_zero hP hdim hg hgP)
    obtain ⟨-, he⟩ := h₂ F K ι W hWm hW0
    show ((resDeg W : ℕ) : ℤ) = intNum F W ![]
    unfold resDeg
    rw [dif_pos hWm.isPrime, he]

end GroundTheory.Heights₂.Heights.FieldNumbers
