import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoundedCusp

theorem mem_SS_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : FD.Wt X.Ψ r) (τ0 : X.Ψ) (h : X.p0 = 0 ∨ X.p0 = r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  exfalso
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  have hmpos := PositiveMinorUnits.mN_pos (MajorantFamilyNorms.hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htop := PositiveMinorUnits.mN_top (MajorantFamilyNorms.hG_of X τ0) X.p0 (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1
  rcases h with h | h
  · rw [h, PositiveMinorUnits.mN_zero] at hmpos
    exact lt_irrefl _ hmpos
  · rw [h, htop] at hmpos
    exact lt_irrefl _ hmpos

end GlobalTheory.BoundedCusp

namespace GlobalTheory

theorem cusp_and_supC_le_of_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (n : ℕ) (f : Rul Xo c) (C : ℝ), 2 ≤ n → Even n → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → f ∈ sec Xo c 0 n → (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 n k) (rdU (U σ) f k) x ≤ C) → 0 ≤ C → f ∈ cusp Xo c U 0 n ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 n f ≤ C := by
  intro E _ _ _ H Dw l Xo c r U n f C hn hev hU hf hb hC
  refine ⟨?_, fun σ xi hσ => ?_⟩
  · rw [mem_cusp]
    refine ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun j => ?_⟩
    obtain ⟨-, -, -, -, hsec, -⟩ := hU σ hσ
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, hev⟩
    obtain ⟨τ0⟩ : Nonempty ((U σ).X j).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ ((U σ).X j).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ).X j).cmType τ).mpr h'))⟩⟩
    have hbd : ((U σ).X j).IsBddSec (laU (U σ) 0 n j) (rdU (U σ) f j) :=
      ⟨hsec _ _ hD f hf j, C, hb σ hσ j⟩
    have hle := ((U σ).X j).p0_le
    by_cases h0 : ((U σ).X j).p0 = 0 ∨ ((U σ).X j).p0 = r
    · exact BoundedCusp.mem_SS_of_definite _ _ τ0 h0 _ hbd
    · refine AR.Up.cuspStatement_holds r _ _ τ0 (by omega) (by omega) ?_ ?_ _ hbd
      · intro i i' h1 h2
        unfold laU
        by_cases h3 : ((U σ).X j).p0 ≤ (i : ℕ)
        · rw [if_pos h3, if_pos (by omega)]
          simp
        · rw [if_neg h3, if_neg (by omega)]
          simp
      · intro i i' h1 h2
        unfold laU
        rw [if_neg (by omega), if_pos (by omega)]
        omega
  · have h1 : lieFac Dw xi (0 : (E →+* ℂ) × ℕ → ℕ) = 1 := by simp [lieFac]
    unfold supC supN
    rw [h1, _root_.one_mul]
    refine ENNReal.toReal_le_of_le_ofReal hC ?_
    exact iSup_le fun p => ENNReal.ofReal_le_ofReal (hb σ hσ p.1 p.2 p.2.2)

end GlobalTheory
