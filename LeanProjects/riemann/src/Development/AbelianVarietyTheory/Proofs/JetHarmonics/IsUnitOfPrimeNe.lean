import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPELOfLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsTer
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentIdFOfLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorsAtPoint

theorem isUnit_of_prime_ne {V : Type} [CommRing V] [IsLocalRing V] {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime)
    (hne : g ≠ g') (hn : ¬ IsUnit ((g : ℕ) : V)) : IsUnit ((g' : ℕ) : V) := by
  have hz : IsCoprime (g : ℤ) (g' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hg hg').2 hne)
  obtain ⟨a, b, hab⟩ : IsCoprime ((g : ℕ) : V) ((g' : ℕ) : V) := by
    simpa using hz.map (Int.castRingHom V)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h₁ | h₁
  · exact absurd (isUnit_of_mul_isUnit_right h₁) hn
  · exact isUnit_of_mul_isUnit_right h₁

section Cast
variable {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem famCast_symm {k k' : ℕ} (e : k = k') (s : Fam Dp F k') : famCast e (famCast e.symm s) = s := by
  subst e; rfl

theorem famCast_sum {k k' : ℕ} (e : k = k') {m : ℕ} (a : Fin m → F) (b : Fin m → Fam Dp F k) :
    famCast e (∑ i, a i • b i) = ∑ i, a i • famCast e (b i) := by
  subst e; rfl

end Cast

theorem nuGe_famCast {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {Dd : DegData V (maximalIdeal V)} {Q : Dd.toPre.X → ℤ} {K : Type} [Field K] [Algebra (FractionRing V) K]
    {v : AddValuation K (WithTop ℚ)} {k k' : ℕ} (e : k = k') {s : Fam Dd.toPre K k} {r : ℚ}
    (h : NuGe Dd Q K v k s r) : NuGe Dd Q K v k' (famCast e s) r := by
  subst e; exact h

theorem unitBall_spanned (hL : Laws) (hT : TwistBaseChangeStatement)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [gr : GrpObj G'] [cm : IsCommMonObj G'] (U' : Unif (maximalIdeal V) D' A' G')
    [md : Module (𝓞 E) D'.toPre.X] :
    letI := H.starRing
    ∀ (oD' : D'.toPre.OAct (𝓞 E)) (oA' : A'.OAct (𝓞 E)) (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'),
      P'.TorsionIso → t'.G = G' → HEq t'.grp gr → HEq t'.comm cm → P'.D = D' → HEq P'.mod md → HEq P'.oD oD' →
      P'.A = A' → HEq P'.oA oA' → HEq P'.U U' →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : D'.toPre.X → ℤ), IsQ D'.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ A'.A) (fun a g => g ≫ oA'.act a)
        (fun n g g' c => WeilIs A'.A A'.L n g g' (unitOn c))),
    ∀ θ : Fam D'.toPre F 1, NuGe D' Q F v 1 θ 0 → ThFrame D' ϖ F θ →
    ∀ θα : Fam D'.toPre F (1 * N), PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ oA'.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro oD' oA' t' P' hP e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  exact ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws hL n1c (GlobalTheory.twisting_statements_of_laws hL hT).1
    (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H V t' P' hP

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → GenPointT := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hne hgo hg'o π π' hπ hπ' hcop hcop' hgnu F _ _ _ _ _ _ v hv I n
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hact s s₂ p w ζ x t₀ t σ' h hbox
  obtain ⟨hs, hs₂, ⟨hw, hζ, hfo⟩, hqx, hxk, hphi, hsm, hexp, hgerm⟩ := hbox
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hπb : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ
  have hπb' : star π' * star (star π') = (g' : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ'
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos hπb
  obtain ⟨pl₂, -, hpl₂⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π * star π') (g' * g) 1 hq
    le_rfl (by rw [star_mul', Nat.cast_mul, ← hπb, ← hπb']; ring)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F
    (g' * g) hq
  obtain ⟨θ, θα, hθν, hθF, hθα⟩ := PowThetaFrame.main hL hL2 hL4 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
    hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  obtain ⟨oA', hoA, hQ', ⟨Dw', ⟨I'⟩⟩, t', P', hP', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    powPEL_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
      hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv I Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  have hcopb : ∃ u u' : 𝓞 E, u * star π' + u' * star (star π') = 1 := by
    obtain ⟨u, u', hu⟩ := hcop'
    exact ⟨u', u, by rw [star_star, ← hu]; ring⟩
  obtain ⟨m, pb, xb, wb, ζb, tb, a, hpx, hxb, hwb, htb, ha, hsum⟩ :=
    unitBall_spanned hL hT E H T.V D' A' G' U' oD' oA' t' P' hP' e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ (star π') g' hg'.pos hπb' hcopb
      (isUnit_of_prime_ne hg hg' hne hgnu) ϖ hϖ _ hQ' F v hv Dw' I' θ hθν hθF θα hθα
      (famCast (Dp := D'.toPre) (F := F) (one_mul g').symm s) (nuGe_famCast _ hs)
  have hs' : s = ∑ i, a i • famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i) := by
    rw [← famCast_sum, ← hsum, famCast_symm]
  let Λ : Fam D'.toPre F g' →ₗ[F] Fam D'.toPre F (g' * g) := (ζ • Φ) ∘ₗ pl
  refine ⟨θ, pl₂ θ, m, a, fun i => gm (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i))), hθν, hθF,
    (hpl₂ _ _).2 rfl, ha, ?_, fun i => ?_⟩
  · have ht : t = Λ s := by
      rw [(DVR.isSmul_iff _ _ _).1 hsm, (hΦ _ _).1 hphi, (hpl _ _).1 hs₂]
      rfl
    rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), ht, hs', map_sum, map_sum]
    simp only [map_smul]
  · obtain ⟨tb₀, h₁, h₂⟩ := htb i
    obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
      PowDescent.descentIdF_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
        hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact oA' hoA θ θα hθα
        (pb i) (wb i) (ζb i) (xb i) tb₀ (tb i) (hpx i) (hxb i) (hwb i).1 (hwb i).2.1 (hwb i).2.2 h₁ h₂
        p w ζ x hw hζ hfo hqx hxk _ _ (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
        ((hpl _ _).2 rfl) ((hΦ _ _).2 rfl) ((DVR.isSmul_iff _ _ _).2 rfl)
    obtain ⟨σ₂, j₁, j₂⟩ := hgmex (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
    refine ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, k₂, fun b => ?_, k₄, k₅, k₆, (hpl₂ _ _).1 k₁ ▸ k₇, k₈, k₉ ▸ j₁,
      (hiff F _ σ₂ _).2 j₂⟩
    have := pA.hom b
    rw [← hoA, ← Category.assoc, k₃, MonObj.one_comp]

end GlobalTheory.GeneratorsAtPoint
