import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenUnitCCOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.NormEqOneOfValuationEqOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace PositivityTheory.RgUd.Exp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isGeneric_of_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W} (h : IsGeneric π)
    (φ : π.Equiv σ) : IsGeneric σ := by
  obtain ⟨ψ, hc, h1, hg⟩ := h
  exact ⟨ψ, hc, h1, hg.of_equiv φ⟩

theorem unitCC_nu_neg (x : IrrGL k) (ω : kˣ →* ℂˣ) (hω : HasCentralChar x.rep ω) (s : ℝ)
    (hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ ((x.1 : ℝ) * s)) : UOrder.UnitCC (x.nu ((-s : ℝ) : ℂ)).rep := by
  refine ⟨ω * absPow k ((-s : ℝ) : ℂ) ^ x.1, GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu x hω _, fun z => ?_⟩
  have hz := nabs_pos' k z
  have hpos : 0 < ‖(((ω * absPow k ((-s : ℝ) : ℂ) ^ x.1) z : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hlog := GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow ω (-s) x.1 z
  rw [hn, Real.log_rpow hz] at hlog
  apply Real.eq_one_of_pos_of_log_eq_zero hpos
  rw [hlog]
  ring

theorem genUnitCCOf : GenUnitCCOf := by
  unfold GenUnitCCOf GenUnitCC
  intro hE hZ k _ _ _ _ _ N V _ _ π hs hi hu hg
  obtain ⟨h, Δ, x, hd, -, hL, ⟨φ⟩⟩ := hZ k N V π hs hi hg
  have hiP : (prodIrr x hd).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv φ hi
  have huP : IsUnitarisable (prodIrr x hd) := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ hu
  have hgP : IsGeneric (prodIrr x hd) := isGeneric_of_equiv hg φ
  have hpos : ∀ j, 0 < (x j).1 := fun j => by
    rw [← (hL j).deg_eq]
    exact Nat.mul_pos (Δ j).len_pos (Δ j).d_pos
  have key : ∀ j, ∃ s : ℝ, |s| < 1 / 2 ∧ UOrder.UnitCC ((x j).nu ((-s : ℝ) : ℂ)).rep := fun j => by
    obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar (x j).2.rep.smooth (x j).2.rep.irr
    obtain ⟨t, ht⟩ := Rpow.norm_eq_nabs_rpow k ω hωs
    have hn0 : ((x j).1 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hpos j).ne'
    have hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ (((x j).1 : ℝ) * (t / (x j).1)) := fun z => by
      rw [ht z, mul_div_cancel₀ t hn0]
    exact ⟨t / (x j).1, hE k h N x hd hiP huP hgP j ω (t / (x j).1) (hpos j) hω hn,
      unitCC_nu_neg (x j) ω hω _ hn⟩
  choose s hs hU using key
  refine ⟨h, fun j => (x j).nu ((-s j : ℝ) : ℂ), fun j => (Δ j).nu ((-s j : ℝ) : ℂ), s,
    fun j => GlobalTheory.isLSeg_nu (hL j) _, hU, hs, ?_⟩
  have hfun : (fun j => ((x j).nu ((-s j : ℝ) : ℂ)).nu (s j)) = x := funext fun j => by
    rw [IrrGL.nu_nu, Complex.ofReal_neg, neg_add_cancel, IrrGL.nu_zero]
  have aux : ∀ y : Fin h → IrrGL k, y = x → ∃ hd' : ∑ j, (y j).1 = N, Nonempty (π.Equiv (prodIrr y hd')) := by
    rintro y rfl
    exact ⟨hd, ⟨φ⟩⟩
  exact aux (fun j => ((x j).nu ((-s j : ℝ) : ℂ)).nu (s j)) hfun

end PositivityTheory.RgUd.Exp
