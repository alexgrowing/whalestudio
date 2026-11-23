import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem exists_rep_restrict {K V G P : Type} [Field K] [AddCommGroup V] [Module K V] [Group G] [Group P] (ℓ : P →* G)
    (a : G → V →ₗ[K] V) (W : Submodule K V) (hW : ∀ g, ∀ f ∈ W, a g f ∈ W) (h1 : ∀ f ∈ W, a 1 f = f)
    (hm : ∀ g g', ∀ f ∈ W, a (g * g') f = a g (a g' f)) :
    ∃ ρ : Representation K P W, ∀ g F, (ρ g F).1 = a (ℓ g) F.1 :=
  ⟨{ toFun := fun g => (a (ℓ g)).restrict (hW (ℓ g))
     map_one' := LinearMap.ext fun F => Subtype.ext (by rw [map_one]; exact h1 _ F.2)
     map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext (by rw [map_mul]; exact hm _ _ _ F.2) },
    fun _ _ => rfl⟩

theorem exists_rep_isLevAct : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) [Group P] (ℓ : P →* (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)), ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp j w), IsLevAct T h j w (fun g => ℓ g) (fun g F => ρ g F) := by
  intro D T h j hj w P _ ℓ
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D T.Q j hpq hp.2.1.2
  have e : cutR T.C j w = T.cuspA j (wtA w) w.n := cutR_eq T.C hj w
  have hnat := fun f (hf : f ∈ cutR T.C j w) => ((mem_cusp _ _ _ _ _ _).1 (e.le hf)).1.1
  exact exists_rep_restrict ℓ (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l)) (cutR T.C j w)
    (fun γ f hf => e.ge (GlobalTheory.LevelCusp.actLev_mem_cuspA D T h j hj w γ f (e.le hf)))
    (fun f hf => actL_one _ _ _ hL.total hL.func hL.one (hnat f hf))
    (fun γ γ' f hf => actL_mul _ _ _ hL.total hL.func hL.mul γ γ' (hnat f hf))

end GlobalTheory.FormTies
