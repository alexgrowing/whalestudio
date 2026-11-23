import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory

theorem levPh_injective_of_levDet_nonZeroDivisor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (χ : S →* (c.F)ˣ) (u : Rul Xo c), u ∈ secRing Xo c → (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → ∀ f ∈ secRing Xo c, (∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ u f h = 0) → f = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c S hpq hA χ u hu hdet f hf hph
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have h1 := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA ⟨u, hu⟩
    have hl : ∀ x : secRing Xo c,
        (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det * x = 0 → x = 0 := by
      intro x hx
      have h2 := congrArg Subtype.val hx
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h2
      apply Subtype.ext
      refine hdet x x.2 ?_
      rw [← h1]
      exact h2
    rw [mem_nonZeroDivisors_iff]
    exact ⟨hl, fun x hx => hl x (by rw [mul_comm]; exact hx)⟩
  have key := (GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ ⟨u, hu⟩ hdet').2.1 ⟨f, hf⟩ (fun h => by
      have h3 := GlobalTheory.LevDesc.coe_tr_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA χ
        (⟨f, hf⟩ * GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA h ⟨u, hu⟩)
      rw [GlobalTheory.LevDesc.tr_apply] at h3
      apply Subtype.ext
      rw [h3]
      exact hph h)
  exact congrArg Subtype.val key

end GlobalTheory
