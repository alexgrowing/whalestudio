import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GeneratorSectionExpansionNuNonnegStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackSectionNuNonnegStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTorsionTranslateSectionNuNonnegStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionRegularOnModelOfNuNonnegStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVR
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT exists_isPullSec)

namespace GlobalTheory.ReachRegular

section BC
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A) {T T' : Over S} (h : T' ⟶ T)

theorem isNormPull_baseChange (φ : A ⟶ A) (a b : ℤ) {s : LB.Sec (LPow A L.L b T)} {t : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L b T')} {t' : LB.Sec (LPow A L.L a T')} (H : IsNormPull A L φ a b s t)
    (hs : IsPullSec A L.L b (h ▷ A) (whiskerRight_snd _ _) s s')
    (ht : IsPullSec A L.L a (h ▷ A) (whiskerRight_snd _ _) t t') : IsNormPull A L φ a b s' t' := by
  have hL := L.isLB
  obtain ⟨α₀, α, h0, hn, hc, htw⟩ := H
  have key : ∀ U : Over S, ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd U A).left, (snd U A ≫ φ).left] ![a, -b]),
      β.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ α₀ (snd U A).left) := fun U => by
    obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd U A).left, (snd U A ≫ φ).left]) (ε' := ![a, -b])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
        · rfl)
      (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd U A).left)
      (DVR.pullGen_isGen _ _ _ _ h0 _)
    exact ⟨α, hα, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩
  obtain ⟨α', hα', hc'⟩ := key T'
  refine ⟨α₀, α', h0, hn, hc', ?_⟩
  have e : endT A T' φ ≫ h ▷ A = h ▷ A ≫ endT A T φ := by ext1 <;> simp [endT]
  obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A b h hs
  obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A a h ht
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
  have v : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J := by
    rw [val_corr hJ hc', val_pull hJ, val_corr hJ hc, val_pull hJ, Category.assoc _ (h ▷ A).left,
      ← Over.comp_left, whiskerRight_snd]
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ, v,
    GlobalTheory.VVRank.sv_of_isTwistPull A htw _ y hJ, Category.assoc, Category.assoc, ← Over.comp_left,
    ← Over.comp_left, e]

theorem isSymAct_baseChange (N : ℕ) (b : T ⟶ A) {s t : LB.Sec (LPow A L.L (N : ℤ) T)}
    {s' t' : LB.Sec (LPow A L.L (N : ℤ) T')} (H : IsSymAct A L N b s t)
    (hs : IsPullSec A L.L N (h ▷ A) (whiskerRight_snd _ _) s s')
    (ht : IsPullSec A L.L N (h ▷ A) (whiskerRight_snd _ _) t t') : IsSymAct A L N (h ≫ b) s' t' := by
  obtain ⟨hb, U, hU, hact⟩ := H
  obtain ⟨U', -, -, h1, h2⟩ := GlobalTheory.ThetaPullback.exists_thetaGrp_pullback S A L.L L.isLB N T T' h U
  exact ⟨by rw [← MonObj.comp_pow, hb, MonObj.comp_one], U', h1 _ _ hU, h2 _ _ _ _ hact hs ht⟩
end BC

set_option maxHeartbeats 1000000 in

theorem regular_of_reach : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), Reach Xo (sOf1 y) k F → Regular C k F := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C hC k F₀ hR
  obtain ⟨-, P, hP⟩ := hC
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hQ : ∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q := by
    choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hch : CharZero T.Fr := charZero_of_injective_ringHom io.injective
  obtain ⟨F, _, _, _, _, _, _, v, hv, -⟩ := GlobalTheory.ClosedValuedField.exists_field_over_cdvr T ϖ hϖ hch
  let xF : Sp F ⟶ Xo.X := spMap (algebraMap T.Fr F) ≫ xOf y
  let h : ptO Xo xF ⟶ ptO Xo (xOf y) := Over.homMk (spMap (algebraMap T.Fr F)) rfl
  have hh : h.left = spMap (algebraMap T.Fr F) := rfl
  have main : 1 ≤ k ∧ ∀ G : SecN Xo xF k,
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((k : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀ G →
      ∀ σ s, SecTieF C.I P F xF k σ G → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0 := by
    induction hR with
    | base => exact ⟨le_rfl, GlobalTheory.T.generator_section_expansion_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh⟩
    | pull k N k' a F₁ F₂ _ hk hN ha hk' hp ih =>
      refine ⟨hk' ▸ Nat.mul_pos ih.1 hN.pos, fun G hG => ?_⟩
      obtain ⟨G₁, hG₁⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
      exact GlobalTheory.T.normalised_pullback_section_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k N k' a G₁ G hk hN.pos ha hk'
        (isNormPull_baseChange _ h _ _ _ hp hG₁ hG) (ih.2 G₁ hG₁)
    | move k b F₁ F₂ _ hm ih =>
      refine ⟨ih.1, fun G hG => ?_⟩
      obtain ⟨G₁, hG₁⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
      exact GlobalTheory.T.symmetric_torsion_translate_section_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k (h ≫ b) G₁ G ih.1
        (isSymAct_baseChange _ h _ b hm hG₁ hG) (ih.2 G₁ hG₁)
  obtain ⟨G, hG⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀
  exact GlobalTheory.T.section_regular_on_model_of_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k F₀ G main.1 hG (main.2 G hG)

end GlobalTheory.ReachRegular
