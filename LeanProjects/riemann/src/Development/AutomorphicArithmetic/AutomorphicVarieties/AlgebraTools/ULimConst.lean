import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.const_bijective :
    ∀ (R ι : Type) [CommRing R] (U : Ultrafilter ι) (m : Ideal R) (Z : Type) [AddCommGroup Z] [Module R Z], IsAdicComplete m Z →
      (∀ j : ℕ, Finite (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) →
      Function.Bijective fun z : Z => ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) fun _ => z := by
  intro R ι _ U m Z _ _ hc hfin
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) (fun _ => a - b) = 0 := by
      have h1 : (fun _ : ι => a - b) = (fun _ : ι => a) - (fun _ : ι => b) := rfl
      rw [h1, map_sub]
      exact sub_eq_zero.2 hab
    rw [ULim.mk_eq_zero] at h0
    refine sub_eq_zero.1 (IsHausdorff.haus hc.toIsHausdorff _ fun j => ?_)
    obtain ⟨_, h⟩ := (h0 j).exists
    exact SModEq.zero.2 h
  · obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
    have hz : ∀ j : ℕ, ∃ z : Z, ∀ᶠ i in (U : Filter ι), p i ≡ z [SMOD (m ^ j • ⊤ : Submodule R Z)] := by
      intro j
      haveI := hfin j
      obtain ⟨q, hq⟩ := Ultrafilter.eq_pure_of_finite
        (U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)))
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨z, ?_⟩
      have h : ({Submodule.Quotient.mk z} : Set (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) ∈
          U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)) := by
        rw [hq]; simp
      exact h
    choose z hz using hz
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := z) (fun {j k} hjk => by
      obtain ⟨i, h1, h2⟩ := ((hz j).and (hz k)).exists
      exact h1.symm.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk))))
    refine ⟨L, ?_⟩
    show ULim.mk _ _ _ _ = _
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
    intro j
    refine (hz j).mono fun i hi => ?_
    exact SModEq.sub_mem.1 (hi.trans (hL j)).symm
