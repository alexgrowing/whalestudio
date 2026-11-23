import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

set_option autoImplicit false

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open GlobalTheory.FlagTan GlobalTheory.FlatLine
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem fChart_exists_val {h : GenFrEx Xo c} (C : Reg.FChart h) {e : Formalism.L2.Pj.Ix Dw → ℤ} {f : Rul Xo c}
    (hf : f ∈ secZ Xo c e) : ∃ b : C.R, (b : Om C.Z) = ((∏ i, C.t i ^ e i : (Om C.Z)ˣ) : Om C.Z) * genVal C.Z f ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S), FrMap ψ C.y z →
        evR Xo c f z = ψ b := by
  have hL : Reg.EvLaws Xo c := (Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
  refine ⟨χ (f q y₀), ?_, fun S _ _ ψ z hz => ?_⟩
  · rw [genVal_apply h, evC, ← evR_frBor hf C.bor,
      evR_eq hf.1 (frMap_comp (χ := C.R.val.comp χ) hy₀ C.gen fun _ => rfl)]
    rfl
  · rw [evR_eq hf.1 (frMap_comp (χ := ψ.comp χ) hy₀ hz fun _ => rfl), AlgHom.comp_apply]

theorem genVal_idem_self (Z : Comp Xo c) : genVal Z (idem Z) = 1 := by
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  rw [genVal_apply h, evC]
  exact evR_idem (liesOn_genFr h Z) (fromTest_of_isLocalRing _)

theorem fChart_evR_idem {h : GenFrEx Xo c} (C : Reg.FChart h) {S : Type} [CommRing S] [Algebra c.F S]
    {ψ : C.R →ₐ[c.F] S} {z : FrPt Xo c S} (hz : FrMap ψ C.y z) : evR Xo c (idem C.Z) z = 1 := by
  obtain ⟨b, hb, hb'⟩ := fChart_exists_val C (idem_mem_secZ C.Z)
  have : b = 1 := Subtype.ext (by simpa [genVal_idem_self] using hb)
  rw [hb' S ψ z hz, this, map_one]

theorem exists_fChart (h : GenFrEx Xo c) (Z : Comp Xo c) : ∃ C : Reg.FChart h, C.Z = Z := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h (Om Z) (genFr h Z)
  refine ⟨C, by_contra fun hne => ?_⟩
  have h1 : evR Xo c (idem C.Z) (genFr h Z) = 0 := evC_eq_zero h (Ne.symm hne) (idem_mem_suppOn C.Z)
  rw [evR_frBor (idem_mem_secZ C.Z) hb, fChart_evR_idem C hz] at h1
  simp at h1

theorem exists_chart_read_at_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  intro E _ _ _ H Dw l Xo c r σ U hU Z
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨C, rfl⟩ := exists_fChart h Z
  haveI := C.sm
  refine ⟨C.R, inferInstance, C.t, fun e f hf => ?_, fun φ hφ => ?_⟩
  · obtain ⟨b, hb, -⟩ := fChart_exists_val C hf
    exact hb ▸ b.2
  · haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    let ψ : C.R →ₐ[c.F] CAt σ := { (φ : C.R →+* CAt σ) with commutes' := fun a => DFunLike.congr_fun hφ a }
    obtain ⟨z, hz⟩ := exists_frMap ψ C.y
    obtain ⟨k, x, s, hs⟩ := hU.2.2.1 z
    have key : ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e,
        toC (σ := σ) (evR Xo c f z) = ((∏ i, (show ℂˣ from s i) ^ e i : ℂˣ) : ℂ) * rdU U f k x.1 := fun e f hf => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_frBor (S := CAt σ) hf hs
    refine ⟨⟨k, x.1⟩, by_contra fun hn => ?_, s, fun e f hf b hb => ?_⟩
    · have h1 := key 0 _ (idem_mem_secZ C.Z)
      rw [rdU_eq_zero U (idem_mem_suppOn C.Z) hn, mul_zero, fChart_evR_idem C hz] at h1
      exact one_ne_zero (α := ℂ) h1
    · obtain ⟨b', hb', h2⟩ := fChart_exists_val C hf
      obtain rfl : b = b' := Subtype.ext (hb.trans hb'.symm)
      exact (h2 _ ψ z hz).symm.trans (key e f hf)

end GlobalTheory.DegCmp
