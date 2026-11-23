import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFiniteness

def LeafSpreadSmooth1 : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadLQFMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {CA CB A B : Scheme.{0}} (cB : CB ⟶ Sp Ω) (γ : CA ⟶ CB) (qB : B ⟶ Sp R) (g : A ⟶ B) (vA : CA ⟶ A)
    (vB : CB ⟶ B), (LocallyOfFinitePresentation qB ∧ QuasiCompact qB ∧ QuasiSeparated qB) →
    (LocallyOfFinitePresentation (g ≫ qB) ∧ QuasiCompact (g ≫ qB) ∧ QuasiSeparated (g ≫ qB)) →
    IsPullback vB cB qB (toR R) → IsPullback vA (γ ≫ cB) (g ≫ qB) (toR R) → γ ≫ vB = vA ≫ g →
    LocallyQuasiFinite γ →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (EA EB : Scheme.{0})
      (qB' : EB ⟶ Sp R') (h : EA ⟶ EB) (rA : EA ⟶ A) (rB : EB ⟶ B), IsPullback rB qB' qB (incl hR) →
      IsPullback rA (h ≫ qB') (g ≫ qB) (incl hR) → h ≫ rB = rA ≫ g → LocallyQuasiFinite h

def LeafSpreadLQFGraph : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (f : D0 ⟶ X) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsPullback v0 c0 q (toR R) → v0 ≫ f = e →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E0 : Scheme.{0})
      (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0), IsPullback r q' q (incl hR) →
      ∀ (hf' : (r ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
        LocallyQuasiFinite (pullback.lift q' (r ≫ f) hf'.symm)

def LeafBaseChangePreR : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR) ∧
      w0 ≫ r0 = v0 ∧ e1 ≫ r0 = r1 ≫ d1 ∧ e2 ≫ r1 = r2 ≫ d2

theorem incl_toK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated) (hSm : LeafSpreadSmooth1)
    (hG : LeafSpreadLQFGraph) (hM : LeafSpreadLQFMap) (hB : LeafBaseChangePreR) :
    LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := by
  intro k _ X p _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 e he hc0 h1 h2 qf0 qf1 qf2 D0 D1 D2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨f0, f1, f2, p0, p1, p2, m1, m2⟩ := id hpre
  obtain ⟨S0, a0, g0, H0⟩ := hSep k Ω R hR c0 q v0 f0 hc0.2.1.toIsSeparated p0
  obtain ⟨S1, a1, g1, H1⟩ := hSep k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1.toIsSeparated p1
  obtain ⟨S2, a2, g2, H2⟩ := hSep k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1.toIsSeparated p2
  obtain ⟨T0, b0, k0, K0⟩ := hSm k Ω R hR c0 q v0 f0 hc0.2.2 p0
  obtain ⟨T1, b1, k1, K1⟩ := hSm k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.2 p1
  obtain ⟨T2, b2, k2, K2⟩ := hSm k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.2 p2
  obtain ⟨G, aG, gG, HG⟩ := hG k p Ω R hR c0 q v0 f e he hf f0 p0 hve qf0
  obtain ⟨M1, aM1, gM1, HM1⟩ := hM k Ω R hR c0 γ1 q d1 v1 v0 f0 f1 p0 p1 m1 qf1
  obtain ⟨M2, aM2, gM2, HM2⟩ := hM k Ω R hR (γ1 ≫ c0) γ2 (d1 ≫ q) d2 v2 v1 f1 f2 p1 p2 m2 qf2
  let T := S0 ⊔ S1 ⊔ S2 ⊔ T0 ⊔ T1 ⊔ T2 ⊔ G ⊔ M1 ⊔ M2
  have gT : T.FG := ((((((((g0.sup g1).sup g2).sup k0).sup k1).sup k2).sup gG).sup gM1).sup gM2)
  have lS0 : S0 ≤ T := (((((((le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have literatureStatementsS1 : S1 ≤ T := (((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have logSupBoundLevelFree : S2 ≤ T := ((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT0 : T0 ≤ T := (((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT1 : T1 ≤ T := ((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT2 : T2 ≤ T := (((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lG : G ≤ T := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have familyMassFirstBound : M1 ≤ T := (le_sup_right).trans le_sup_left
  have familyMassSecondBound : M2 ≤ T := le_sup_right
  have hRT : R ≤ T := a0.trans lS0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2, n0, n1, n2⟩ :=
    hB k Ω R T hRT c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  have hf' : (r0 ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [Category.assoc, hf, ← Category.assoc, Q0.w, Category.assoc, incl_toK]
  haveI := f0.2.1; haveI := f1.2.1; haveI := f2.2.1
  refine ⟨T, gT, E0, E1, E2, q', e1, e2, r0 ≫ f, w0, w1, w2, hf', ?_⟩
  exact ⟨H0 T lS0 hRT E0 q' r0 Q0, MorphismProperty.of_isPullback (P := @QuasiCompact) Q0 inferInstance,
    K0 T lT0 hRT E0 q' r0 Q0,
    H1 T literatureStatementsS1 hRT E1 (e1 ≫ q') r1 Q1, MorphismProperty.of_isPullback (P := @QuasiCompact) Q1 inferInstance,
    K1 T lT1 hRT E1 (e1 ≫ q') r1 Q1,
    H2 T logSupBoundLevelFree hRT E2 (e2 ≫ e1 ≫ q') r2 Q2, MorphismProperty.of_isPullback (P := @QuasiCompact) Q2 inferInstance,
    K2 T lT2 hRT E2 (e2 ≫ e1 ≫ q') r2 Q2,
    HG T lG hRT E0 q' r0 Q0 hf', HM1 T familyMassFirstBound hRT E1 E0 q' e1 r1 r0 Q0 Q1 n1,
    HM2 T familyMassSecondBound hRT E2 E1 (e1 ≫ q') e2 r2 r1 Q1 Q2 n2, P0, P1, P2, c1, c2,
    by rw [← Category.assoc, n0, hve]⟩

end LateralTheory.E.SpreadingOutQuasiFiniteness

end
