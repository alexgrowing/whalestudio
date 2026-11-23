import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitIdem

section Single

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

open Classical in

def singleAt (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) : AFplus L :=
  RestrictedProduct.mk (Pi.single v t) (by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _)

theorem singleAt_self (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) :
    singleAt (L := L) v t v = t := by
  classical
  show Pi.single v t v = t
  exact Pi.single_eq_same v t

theorem singleAt_ne {v w : HeightOneSpectrum (𝓞 L⁺)} (t : v.adicCompletion L⁺) (h : w ≠ v) :
    singleAt (L := L) v t w = 0 := by
  classical
  show Pi.single v t w = 0
  exact Pi.single_eq_of_ne h t

theorem singleAt_int (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) (ht : Valued.v t ≤ 1) :
    ∀ w, singleAt (L := L) v t w ∈ w.adicCompletionIntegers L⁺ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [singleAt_self]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ht
  · rw [singleAt_ne t h]
    exact zero_mem _

theorem one_tmul_algebraMap (c : L⁺) :
    ((1 : L) ⊗ₜ[L⁺] algebraMap L⁺ (AFplus L) c : AL L) = (algebraMap L⁺ L c) ⊗ₜ[L⁺] (1 : AFplus L) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

end Single

theorem exists_idem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L),
    ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧
      s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧
      ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  intro L _ _ _ s
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep (L := L) s
  set cc := IsCMField.complexConj L with hcc
  set α := s.i (e : L) with hα
  set β := s.i (cc (e : L)) with hβ
  have hαβ : Valued.v (α - β) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (he'.trans_eq he.symm)]; exact he
  have hne : α - β ≠ 0 := by
    intro h; rw [h, map_zero] at hαβ; exact zero_ne_one hαβ
  set a := (α - β)⁻¹ with ha
  set b := -β * a with hb
  have hva : Valued.v a = 1 := by rw [ha, map_inv₀, hαβ, inv_one]
  have hvb : Valued.v b ≤ 1 := by
    rw [hb, map_mul, Valuation.map_neg, hva, mul_one]; exact he'.le
  have hT : cc ((e : L) + cc (e : L)) = (e : L) + cc (e : L) := by
    rw [map_add, IsCMField.complexConj_apply_apply, add_comm]
  have hN : cc ((e : L) * cc (e : L)) = (e : L) * cc (e : L) := by
    rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  let T : maximalRealSubfield L := ⟨(e : L) + cc (e : L), (IsCMField.complexConj_eq_self_iff L _).1 hT⟩
  let N : maximalRealSubfield L := ⟨(e : L) * cc (e : L), (IsCMField.complexConj_eq_self_iff L _).1 hN⟩
  have hTL : algebraMap (maximalRealSubfield L) L T = (e : L) + cc (e : L) := rfl
  have hNL : algebraMap (maximalRealSubfield L) L N = (e : L) * cc (e : L) := rfl
  have hTv : algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) T = α + β := by
    rw [hα, hβ, ← map_add, ← hTL, AlgHom.commutes]
  have hNv : algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) N = α * β := by
    rw [hα, hβ, ← map_mul, ← hNL, AlgHom.commutes]
  set A : AFplus L := singleAt s.v a with hA
  set B : AFplus L := singleAt s.v b with hB
  let ι := (Algebra.TensorProduct.includeRight : AFplus L →ₐ[maximalRealSubfield L] AL L)
  have hι : ∀ x : AFplus L, ι x = (1 : L) ⊗ₜ x := fun x => rfl
  set E : AL L := (e : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hEdef
  have hinv : (α - β) * a = 1 := mul_inv_cancel₀ hne
  have hE : E * E = ι (algebraMap _ _ T) * E - ι (algebraMap _ _ N) := by
    rw [hι, hι, one_tmul_algebraMap, one_tmul_algebraMap, hEdef, hTL, hNL,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.sub_tmul]
    congr 1; ring
  have hcE : conjAL L E = ι (algebraMap _ _ T) - E := by
    rw [hι, one_tmul_algebraMap, hTL, hEdef, ← TensorProduct.sub_tmul, add_sub_cancel_left]
    simp [conjAL, Algebra.TensorProduct.map_tmul, hcc]
  have hcι : ∀ x : AFplus L, conjAL L (ι x) = ι x := by
    intro x; rw [hι]; simp [conjAL, Algebra.TensorProduct.map_tmul]

  have ext' : ∀ x y : AFplus L, (∀ w, x w = y w) → x = y := fun x y h => RestrictedProduct.ext _ _ h
  have comp : ∀ w, (A w = 0 ∧ B w = 0) ∨ (w = s.v) := by
    intro w; by_cases h : w = s.v
    · exact Or.inr h
    · exact Or.inl ⟨singleAt_ne a h, singleAt_ne b h⟩
  have hAv : A s.v = a := singleAt_self _ _
  have hBv : B s.v = b := singleAt_self _ _
  have hTw : (algebraMap (maximalRealSubfield L) (AFplus L) T) s.v = α + β := hTv
  have hNw : (algebraMap (maximalRealSubfield L) (AFplus L) N) s.v = α * β := hNv
  have hP : algebraMap _ _ T * A * A + (A * B + A * B) = A := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show _ * A w * A w + (A w * B w + A w * B w) = A w
      rw [h1, h2]; ring
    · show _ * A s.v * A s.v + (A s.v * B s.v + A s.v * B s.v) = A s.v
      rw [hAv, hBv, hb]; erw [hTw]
      linear_combination a * hinv
  have hQ : B * B - algebraMap _ _ N * A * A = B := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show B w * B w - _ * A w * A w = B w
      rw [h1, h2]; ring
    · show B s.v * B s.v - _ * A s.v * A s.v = B s.v
      rw [hAv, hBv, hb]; erw [hNw]
      linear_combination (-β * a) * hinv
  have hR : algebraMap _ _ N * A * A + algebraMap _ _ T * A * B + B * B = 0 := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show _ * A w * A w + _ * A w * B w + B w * B w = 0
      rw [h1, h2]; ring
    · show _ * A s.v * A s.v + _ * A s.v * B s.v + B s.v * B s.v = 0
      rw [hAv, hBv, hb]; erw [hNw, hTw]
      ring
  have hS : (algebraMap _ _ T * A + (B + B) : AFplus L) s.v = 1 := by
    show _ * A s.v + (B s.v + B s.v) = 1
    rw [hAv, hBv, hb]; erw [hTw]
    linear_combination hinv
  have hP' := congrArg ι hP
  have hQ' := congrArg ι hQ
  have hR' := congrArg ι hR
  simp only [map_add, map_mul, map_sub, map_zero] at hP' hQ' hR'
  have hpE : s.proj E = α := by
    rw [hEdef]; unfold SplitPlace.proj
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, mul_one]
  have hpι : ∀ x : AFplus L, s.proj (ι x) = x s.v := by
    intro x; rw [hι]; unfold SplitPlace.proj
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]; rfl
  have hcomp : ∀ w (x : AFplus L), compAt L w (ι x) = (1 : L) ⊗ₜ (x w) := by
    intro w x; rw [hι]; unfold compAt
    erw [Algebra.TensorProduct.map_tmul]
    rfl
  have hconjε : conjAL L (E * ι A + ι B) = (ι (algebraMap _ _ T) - E) * ι A + ι B := by
    rw [map_add, map_mul, hcE, hcι, hcι]
  refine ⟨E * ι A + ι B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (ι A) ^ 2 * hE + E * hP' + hQ'
  · rw [hconjε]
    linear_combination (-(ι A) ^ 2) * hE + hR'
  · refine Subring.add_mem _ (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨A, singleAt_int _ _ hva.le, rfl⟩)))
      (Subring.subset_closure (Or.inr ⟨B, singleAt_int _ _ hvb, rfl⟩))
  · rw [map_add, map_mul, hpE, hpι, hpι, hAv, hBv, hb]
    linear_combination hinv
  · have h : E * ι A + ι B + conjAL L (E * ι A + ι B) = ι (algebraMap _ _ T * A + (B + B)) := by
      rw [hconjε]; simp only [map_add, map_mul]; ring
    rw [h, hcomp, hS]; rfl
  · intro w hw
    rcases comp w with ⟨h1, h2⟩ | h
    · refine ⟨?_, ?_⟩
      · rw [map_add, map_mul, hcomp, hcomp, h1, h2]; simp
      · rw [hconjε, map_add, map_mul, hcomp, hcomp, h1, h2]; simp
    · exact absurd h hw

end GlobalTheory.SplitIdem
