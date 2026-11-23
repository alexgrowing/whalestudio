import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ResTilt

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

abbrev red : (Wq l a)⟦X⟧ →+* (Fq l a)⟦X⟧ := PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a))

def sec (f : (Fq l a)⟦X⟧) : (Wq l a)⟦X⟧ := mk fun n => WittVector.teichmuller l (coeff n f)

theorem red_sec : Function.RightInverse (sec l a) (red l a) := fun f =>
  PowerSeries.ext fun n => by simp [red, sec, coeff_map, WittVector.constantCoeff_apply]

theorem red_l : red l a (l : (Wq l a)⟦X⟧) = 0 := by
  rw [map_natCast]; exact l_eq_zero l a

omit [NeZero a] in

theorem sub_teich_dvd (x : Ainf l) : ∃ z, x = WittVector.teichmuller l (x.coeff 0) + (l : Ainf l) * z := by
  have h : x - WittVector.teichmuller l (x.coeff 0) ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨z, by linear_combination -hz⟩

end GlobalTheory.BSP.ResTilt

open GlobalTheory.BSP.ResTilt in

theorem GlobalTheory.BSP.exists_resTilt_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧),
      (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) =
        (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  let φ : bk.S →+* OCb l := (WittVector.constantCoeff (p := l) (R := OCb l)).comp bk.ev
  have hker : RingHom.ker (red l bk.a) ≤ RingHom.ker φ := fun s hs => by
    obtain ⟨t, rfl⟩ := dvd_of_map_eq_zero l bk.a s hs
    rw [RingHom.mem_ker, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  let ek : (Fq l bk.a)⟦X⟧ →+* OCb l := (red l bk.a).liftOfRightInverse (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩
  have hek : ∀ s, ek (red l bk.a s) = φ s := fun s =>
    (red l bk.a).liftOfRightInverse_comp_apply (sec l bk.a) (red_sec l bk.a) ⟨φ, hker⟩ s

  let P : OCb l → (Fq l bk.a)⟦X⟧ := fun y => red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l y))
  have hwd : ∀ x : Ainf l, red l bk.a (tb.c tb.i₀ x) = P (x.coeff 0) := fun x => by
    obtain ⟨z, hz⟩ := sub_teich_dvd l x
    conv_lhs => rw [hz]
    have e : (l : Ainf l) = bk.ev (l : bk.S) := (map_natCast _ _).symm
    rw [map_add, e, tb.c_mul, map_add, map_mul, red_l l bk.a, zero_mul, add_zero]
  let pr : OCb l →+ (Fq l bk.a)⟦X⟧ :=
    { toFun := P
      map_zero' := by simp [P]
      map_add' := fun y y' => by
        have h := hwd (WittVector.teichmuller l y + WittVector.teichmuller l y')
        rw [map_add, map_add] at h
        have h0 : (WittVector.teichmuller l y + WittVector.teichmuller l y').coeff 0 = y + y' := by
          rw [← WittVector.constantCoeff_apply, map_add]; simp [WittVector.constantCoeff_apply]
        rw [h0] at h
        exact h.symm }
  have hmul : ∀ a y, pr (ek a * y) = a * pr y := fun f y => by
    obtain ⟨s, rfl⟩ : ∃ s, red l bk.a s = f := ⟨sec l bk.a f, red_sec l bk.a f⟩
    have h := hwd (bk.ev s * WittVector.teichmuller l y)
    rw [tb.c_mul, map_mul] at h
    change P (ek (red l bk.a s) * y) = red l bk.a s * P y
    have e : (bk.ev s * WittVector.teichmuller l y).coeff 0 = φ s * y := by
      rw [← WittVector.constantCoeff_apply, map_mul, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rfl
    rw [hek, ← e]
    exact h.symm
  have hone : pr 1 = 1 := by
    change red l bk.a (tb.c tb.i₀ (WittVector.teichmuller l 1)) = 1
    rw [map_one, ← tb.b_i₀, tb.c_self, map_one]
  refine ⟨ek, pr, fun s => hek s, ?_, hmul, hone⟩
  refine Function.LeftInverse.injective (g := pr) fun f => ?_
  have := hmul f 1
  rwa [mul_one, hone, mul_one] at this
