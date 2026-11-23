import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FullLevelAction

open GlobalTheory.LevelActionLaws

theorem actLaws_levFull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) :
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (y y' : FrPt Xo c S) =>
        levActR (Xo := Xo) (c := c) (levFull Dw l) g' y y') := by
  obtain ⟨⟨ι, hι, hone⟩, hmul, hnb⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨ρ, ν, i, h⟩ := exists_move hpq hA Xo g
    obtain ⟨y', hy'⟩ := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).1
    exact ⟨y', ρ, ν, i, h, hy'⟩
  · intro g S _ _ y y' y'' h' h''
    obtain ⟨ρ, ν, i, h, hm⟩ := h'
    have hm' := frMove_transfer hpq hA Xo c g i h h''
    obtain rfl := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y').2.1
  · intro S _ _ y
    refine ⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (eta_congr Xo (liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  · intro g g' S _ _ y y' y'' h h'
    obtain ⟨ρ, ν, i, h, hm⟩ := h
    obtain ⟨ρ', ν', i', h', hm'⟩ := h'
    obtain ⟨μ, hμ, hc⟩ := hmul ρ ρ' ν ν'
    refine ⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hm hm'⟩
    · rw [Category.assoc, h'.1, h.1]
    · have e : Xo.univ.eta ((levFull Dw l (g * g')).1 a) =
          Xo.univ.eta ((levFull Dw l g).1 ((levFull Dw l g').1 a)) :=
        eta_congr Xo (liftLa_mul_sub g g' a)
      rw [e, hμ, ← Category.assoc, h.2.1, Category.assoc, h'.2.1, Category.assoc]
    · have e : (levFull Dw l (g * g')).2 a = (levFull Dw l g).2 ((levFull Dw l g').2 a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  · intro g S T _ _ _ _ φ y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)
  · intro g S _ _ t y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)

theorem actLev_levFull : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  intro D Q j hpq hA
  exact actLaws_levFull (Q.Xo j) Q.c hpq (by rw [hA]; exact Nat.coprime_one_left _)

end GlobalTheory.FullLevelAction
