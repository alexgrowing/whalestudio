import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory.InterpPos

theorem interp_isPosFrame : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ}, IsPosFrame U H₀ → IsPosFrame U H → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, s z ∈ Icc (0 : ℝ) 1) → IsPosFrame U (interp H₀ H s) := by
  intro ι n _ _ _ U H₀ H s h₀ h hs hs01
  refine ⟨h₀.isOpen, fun a b => ?_, fun z hz => ?_⟩
  · have e : (fun x => interp H₀ H s x a b) = fun x =>
        ((1 - s x : ℝ) : ℂ) * H₀ x a b + ((s x : ℝ) : ℂ) * H x a b := by
      funext x; simp [interp]
    rw [e]
    have h1 : ContDiffOn ℝ ∞ (fun x => ((1 - s x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
    have h2 : ContDiffOn ℝ ∞ (fun x => ((s x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hs
    exact (h1.mul (h₀.smooth a b)).add (h2.mul (h.smooth a b))
  · obtain ⟨hs0, hs1⟩ := hs01 z hz
    rcases hs1.lt_or_eq with hlt | heq
    · have hA : (((1 - s z : ℝ) : ℂ) • H₀ z).PosDef :=
        (h₀.posDef z hz).smul (by exact_mod_cast (sub_pos.2 hlt))
      have hB : (((s z : ℝ) : ℂ) • H z).PosSemidef :=
        (h.posDef z hz).posSemidef.smul (by exact_mod_cast hs0)
      exact hA.add_posSemidef hB
    · have hA : (((1 - s z : ℝ) : ℂ) • H₀ z).PosSemidef :=
        (h₀.posDef z hz).posSemidef.smul (by rw [heq]; simp)
      have hB : (((s z : ℝ) : ℂ) • H z).PosDef :=
        (h.posDef z hz).smul (by rw [heq]; simp)
      show (((1 - s z : ℝ) : ℂ) • H₀ z + ((s z : ℝ) : ℂ) • H z).PosDef
      rw [add_comm]; exact hB.add_posSemidef hA

end GlobalTheory.InterpPos
