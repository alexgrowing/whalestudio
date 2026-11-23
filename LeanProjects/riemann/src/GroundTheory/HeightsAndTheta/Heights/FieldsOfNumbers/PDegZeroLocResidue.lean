import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000

namespace DegZeroLocResidue

variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}

local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)

omit [DecidableEq K] in

theorem fr_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {h : MRing ι F} (hh : h ∉ Q) :
    fr Q h ≠ 0 := by
  rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]

omit [DecidableEq K] in

theorem residue_eq (hPW : P ≤ W) {f g f' g' : MRing ι F} (hg : g ∉ W) (hg' : g' ∉ W)
    (h : fr P f / fr P g = fr P f' / fr P g') : fr W f / fr W g = fr W f' / fr W g' := by
  rw [div_eq_div_iff (fr_ne_zero P fun h => hg (hPW h)) (fr_ne_zero P fun h => hg' (hPW h)),
    ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
  rw [div_eq_div_iff (fr_ne_zero W hg) (fr_ne_zero W hg'), ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, Ideal.Quotient.eq.mpr (hPW (Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h)))]

variable (P W) in
open Classical in

def res (x : FractionRing (MRing ι F ⧸ P)) : FractionRing (MRing ι F ⧸ W) :=
  if h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 then
    fr W h.choose.1 / fr W h.choose.2 else 0

omit [DecidableEq K] in

theorem res_eq (hPW : P ≤ W) {x : FractionRing (MRing ι F ⧸ P)} {f g : MRing ι F} (hg : g ∉ W)
    (hx : x = fr P f / fr P g) : res P W x = fr W f / fr W g := by
  have h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 := ⟨(f, g), hg, hx⟩
  rw [res, dif_pos h]
  exact residue_eq hPW h.choose_spec.1 hg (h.choose_spec.2.symm.trans hx)

theorem exists_rep (x : degZeroLoc P {W}) : ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ W ∧ (x : FractionRing (MRing ι F ⧸ P)) = fr P f / fr P g := by
  obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K ι P {W}
    (by rintro _ rfl; infer_instance) x x.2
  exact ⟨b, f, g, hf, hg, hgW W rfl, hx⟩

def ρ (hPW : P ≤ W) : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W) where
  toFun x := res P W x
  map_one' := by
    have h1 : (1 : MRing ι F) ∉ W := (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
    rw [res_eq hPW (f := 1) (g := 1) h1 (by simp)]; simp
  map_mul' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * f') hPW hgg
      (by rw [Subalgebra.coe_mul, hx, hy, div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]),
      div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]
  map_zero' := by
    rw [res_eq hPW (f := 0) (g := 1) ((Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top') (by simp)]
    simp
  map_add' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * g' + g * f') hPW hgg
      (by rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (fr_ne_zero P fun h => hg (hPW h))
        (fr_ne_zero P fun h => hg' (hPW h))]; simp only [map_add, map_mul]),
      div_add_div _ _ (fr_ne_zero W hg) (fr_ne_zero W hg')]
    simp only [map_add, map_mul]

theorem ρ_apply (hPW : P ≤ W) (x : degZeroLoc P {W}) : ρ hPW x = res P W x := rfl

theorem inv_mem (hPW : P ≤ W) {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hfW : f ∉ W) : fr P g / fr P f ∈ degZeroLoc P {W} :=
  div_mem_degZeroLoc P {W} hg hf (fun h => hfW (hPW h)) (by rintro _ rfl; exact hfW)

theorem proof : DegZeroLocResidue.Statement := by
  intro F _ K _ ι P _ W _ hPW
  refine ⟨ρ hPW, fun x b f g _ _ hg hx => res_eq hPW hg hx, fun x => ⟨?_, ?_⟩, fun z => ⟨?_, ?_⟩⟩
  · rintro h0 ⟨y, hy, hxy⟩
    have h1 : ρ hPW (x * ⟨y, hy⟩) = 1 := by rw [show x * ⟨y, hy⟩ = 1 from Subtype.ext hxy, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro hn
    by_contra h0
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx] at h0
    have hfW : f ∉ W := fun h => h0 (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
    refine hn ⟨_, inv_mem hPW hf hg hfW, ?_⟩
    rw [hx, div_mul_div_comm, mul_comm (fr P f), div_self (mul_ne_zero
      (fr_ne_zero P fun h => hgW (hPW h)) (fr_ne_zero P fun h => hfW (hPW h)))]
  · intro hz
    let E : IntermediateField F (FractionRing (MRing ι F ⧸ W)) :=
      { carrier := Set.range (ρ hPW)
        mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
        one_mem' := ⟨1, map_one _⟩
        zero_mem' := ⟨0, map_zero _⟩
        algebraMap_mem' := fun c => ⟨algebraMap F _ c, by
          rw [ρ_apply, res_eq hPW (f := C c) (g := 1) ((Ideal.ne_top_iff_one W).mp
            Ideal.IsPrime.ne_top') (by
              show algebraMap F (FractionRing (MRing ι F ⧸ P)) c = _
              rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P),
                ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq])]
          rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ W),
            ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]⟩
        inv_mem' := by
          rintro _ ⟨x, rfl⟩
          by_cases h0 : ρ hPW x = 0
          · rw [h0, inv_zero]; exact ⟨0, map_zero _⟩
          obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
          rw [ρ_apply, res_eq hPW hgW hx] at h0 ⊢
          have hfW : f ∉ W := fun h => h0 (by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
          exact ⟨⟨_, inv_mem hPW hf hg hfW⟩, by rw [ρ_apply, res_eq hPW hfW rfl, inv_div]⟩ }
    have hle : homFracDegZero W ≤ E := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨⟨_, div_mem_degZeroLoc P {W} hf hg (fun h => hgW (hPW h)) (by rintro _ rfl; exact hgW)⟩,
        res_eq hPW hgW rfl⟩
    exact hle hz
  · rintro ⟨x, rfl⟩
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx]
    exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgW, rfl⟩

end DegZeroLocResidue

end

end GroundTheory.Heights₂.Heights.FieldNumbers
