import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMoveStatement
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
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

theorem fromTest_mvPt {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem levAct_mem_Mlat : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w), IsLevAct T h j w ℓ act → ∀ g, ∀ F ∈ (recB h.toLawsCore).Mlat j w, act g F ∈ (recB h.toLawsCore).Mlat j w := by
  intro D T h j hj w P ℓ act hact g F hF
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  have hc : (F.1 : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hc).1.1
  rintro la _ ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total (ℓ g) y.1
  let y' : IntFr (T.Q.Xo j) T.Q.c S io :=
    ⟨_, fromTest_mvPt hL (ℓ g) y.2.1, GlobalTheory.T.integral_framedPoint_of_level_move _ _ _ _ _ _ (levFull (T.Q.Dw j) T.Q.l (ℓ g)) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' F.1) := hF la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (act g F).1 = evI y' F.1 := by
    rw [hact g F]
    exact evalAt_actL hL (h.evalWD j hj) frMap_trans_id (ℓ g) hnat y.1
  show 0 ≤ nval S.V e (evI y (act g F).1)
  rw [e1]
  exact h0

end GlobalTheory.FormTies
