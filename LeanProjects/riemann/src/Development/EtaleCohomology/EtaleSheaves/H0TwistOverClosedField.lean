import Development.EtaleCohomology.EtaleSheaves.EtaleChapterEFour

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def Hyps : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧
    D1 ∧ D2 ∧ D3 ∧ E1 ∧ E2 ∧ E3

abbrev Sp (A : Type) [CommRing A] : Scheme.{0} := Spec (CommRingCat.of A)

abbrev pl (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X) (m : ℤ) : Ht q (sch.obj X) m i →+ Ht q (sch.obj Y) m i :=
  pull (ZMod q) (sch.map f) (tw q i) m

def IsCurve {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) : Prop :=
  IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c

def SmP {Y B : Scheme.{0}} (p : Y ⟶ B) (V : B.Opens) : Prop := IsProper p ∧ Smooth (p ∣_ V)

abbrev fibMap {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) : pullback (g ≫ p) s ⟶ pullback p s :=
  pullback.map (g ≫ p) s p s g (𝟙 _) (𝟙 _) (by simp) (by simp)

def H0TwistOverClosedField : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  Finite (Ht q (sp Ω) 0 i) ∧ ∀ {X : Scheme.{0}} [ConnectedSpace X] (c : X ⟶ Sp Ω), Function.Bijective (pl q i c 0)

def LeafPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p], topologicalKrullDim X ≤ 0 → ∀ n i : ℤ,
  Finite (Ht q (sch.obj X) n i)

def LeafComp : Prop := Hyps → ∀ (q : ℕ) (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (n i : ℤ),
  (∀ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι → IsIntegral Z → Finite (Ht q (sch.obj Z) n i)) →
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsProper f ∧ Surjective f ∧ Finite (Ht q (sch.obj Y) n i)

def LeafDesc : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) →
  ∀ {Y X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (f : Y ⟶ X) [IsProper f] [Surjective f] (i : ℤ), Eqv _ (cechAug f) (tw q i)

def LeafSS : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] (n : ℤ),
  Eqv R (cechAug f) F → (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → ∀ m < n, Finite (H R (sch.obj Z) F m)) →
  Finite (pull R (sch.map f) F n).ker

def LeafUnits : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range)

def LeafPic : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → Finite {c : CommRing.Pic B // c ^ q = 1}

def LeafKum : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B],
  IsUnit (q : k) → Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) → Finite {c : CommRing.Pic B // c ^ q = 1} →
  ∀ i : ℤ, Finite (Ht q (sp B) 1 i)

def LeafCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  (∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B], Finite (Ht q (sp B) 1 i)) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → Finite (Ht q (sch.obj C) 1 i) ∧ Finite (Ht q (sch.obj C) 2 i) ∧
    ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj C) m i)

def LeafKill : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → Finite (Ht q (sch.obj C) m i) →
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m = 0

def Family {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B W Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (ι : W ⟶ B) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim X ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeo : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → Family (k := k) X c0 γ1 γ2

def LeafSpec : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (_ : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0), SmP p V → SmP (g ≫ p) V →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ B), Set.range s ⊆ V →
  ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ : C1 ⟶ C0) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1),
    IsPullback u0 c0 p s → IsPullback u1 (γ ≫ c0) (g ≫ p) s → γ ≫ u0 = u1 ≫ g →
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, Subsingleton (Ht q (sch.obj C0) m i) → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧
    (∀ m, pl q i γ m = 0 → pl q i (fibMap g p t) m = 0) ∧
    (Function.Bijective (pl q i (γ ≫ c0) 0) → Function.Bijective (pl q i (pullback.snd (g ≫ p) t) 0))

def LeafGhost : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (a : Ht q (sch.obj Y0) n i), pl q i (pullback.fst p ι) n a = 0 →
    ∃ b : Ht q (sch.obj B) n i, pl q i (g2 ≫ g1 ≫ p) n b = pl q i (g2 ≫ g1) n a

theorem fin_of {A C D E : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] (φ : A →+ C)
    (r : A →+ D) (ψ : E →+ C) [Finite D] [Finite E] (hk : Finite φ.ker) (h : ∀ a, r a = 0 → ∃ b, ψ b = φ a) : Finite A := by
  rw [AddMonoidHom.finite_iff_finite_ker_range r]
  refine ⟨?_, inferInstance⟩
  rw [AddMonoidHom.finite_iff_finite_ker_range (φ.comp r.ker.subtype)]
  constructor
  · exact Finite.of_injective (fun x : (φ.comp r.ker.subtype).ker => (⟨x.1.1, x.2⟩ : φ.ker))
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker => z.1) hxy)))
  · have : (Set.range ψ).Finite := Set.finite_range _
    refine Set.Finite.subset this ?_
    rintro _ ⟨a, rfl⟩
    exact h a.1 a.2

theorem pl_comp (q : ℕ) (i : ℤ) {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (m : ℤ) (x : Ht q (sch.obj X) m i) :
    pl q i (g ≫ f) m x = pl q i g m (pl q i f m x) := by
  rw [← pull_comp, ← Functor.map_comp]

theorem goal_of (hH0 : H0TwistOverClosedField) (hPt : LeafPt) (hComp : LeafComp) (hDesc : LeafDesc) (hSS : LeafSS) (hU : LeafUnits)
    (hPic : LeafPic) (hKum : LeafKum) (hCurve : LeafCurve) (hKill : LeafKill) (hGeo : LeafGeo) (hSpec : LeafSpec)
    (hGhost : LeafGhost) : LateralTheory.E.EtaleChapterEFour := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3
  have hy : Hyps := ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩
  intro q _ k _ _ hq X p _ n i
  have step : ∀ n : ℤ, (∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < n, Finite (Ht q (sch.obj X) m i)) →
      ∀ (e : WithBot ℕ∞) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
    intro n Q
    have ker : ∀ (X Y : Scheme.{0}) (p : X ⟶ Sp k) (f : Y ⟶ X), IsProper p → IsProper f → Surjective f →
        Finite (pl q i f n).ker := fun X Y p f _ _ _ =>
      hSS hy _ _ f n (hDesc hy q k hq p f i) (fun Z g _ => Q Z (g ≫ p) inferInstance)
    intro e
    induction e using WellFoundedLT.induction with
    | ind e IH =>
    have int : ∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → IsIntegral X → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
      intro X p _ _ he
      rcases le_or_gt (topologicalKrullDim X) 0 with h0 | h0
      · exact hPt hy q k hq p h0 n i
      obtain ⟨Ω, _, _, _, C0, c0, hc0, hall⟩ := hGeo k p h0
      have hΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap k Ω)
      have hc : ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → _ := fun c => hCurve hy q Ω hΩ i
        (fun B _ _ _ _ => hKum hy q Ω B hΩ (hU q Ω B) (hPic hy q Ω B hΩ) i) c
      obtain ⟨C1, γ1, hc1, s1, z1⟩ := hKill hy q Ω hΩ c0 hc0 2 i (by norm_num) (hc c0 hc0).2.1
      obtain ⟨C2, γ2, hc2, s2, z2⟩ := hKill hy q Ω hΩ (γ1 ≫ c0) hc1 1 i (by norm_num) (hc _ hc1).1
      obtain ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, _, _, _, hV, hs, m0, m1, m2, f1, f2, dB, dW,
        P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 hc1 hc2 s1 s2
      have := m0.1
      have := hc2.1
      have fB := IH _ (dB.trans_le he) B b inferInstance le_rfl
      have fW := IH _ (dW.trans_le he) (pullback π ι) (pullback.fst π ι ≫ π ≫ b) inferInstance le_rfl
      have G := hGhost hy q k hq i b ι V hV π g1 g2 m0.1 m1.1 m2.1 (fun A _ t hA ht => by
        have S1 := hSpec hy q k hq i b V π g1 m0 m1 Ω s hs c0 γ1 u0 u1 P0 P1 w1 A t hA ht
        have S2 := hSpec hy q k hq i b V (g1 ≫ π) g2 m1 m2 Ω s hs (γ1 ≫ c0) γ2 u1 u2 P1 P2 w2 A t hA ht
        exact ⟨fun m hm => S1.1 m ((hc c0 hc0).2.2 m hm), S1.2.1 2 z1, S2.2.1 1 z2,
          S2.2.2 ((hH0 hy q Ω hΩ i).2 _)⟩) n
      refine fin_of (pl q i (g2 ≫ g1 ≫ h) n) (pl q i (pullback.fst π ι ≫ h) n) (pl q i (g2 ≫ g1 ≫ π) n)
        (ker X Y2 p _ inferInstance f1 f2) (fun a ha => ?_)
      rw [pl_comp] at ha
      obtain ⟨x, hx⟩ := G _ ha
      exact ⟨x, by rw [hx, ← pl_comp, Category.assoc]⟩
    intro X p _ he
    obtain ⟨Y, f, f1, f2, f3⟩ := hComp hy q k p n i (fun Z ι _ _ =>
      int Z (ι ≫ p) inferInstance inferInstance (ι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans he))
    have := ker X Y p f inferInstance f1 f2
    rw [AddMonoidHom.finite_iff_finite_ker_range (pl q i f n)]
    exact ⟨this, inferInstance⟩
  have all : ∀ (N : ℕ) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < (N : ℤ), Finite (Ht q (sch.obj X) m i) := by
    intro N
    induction N with
    | zero =>
      intro X p _ m hm
      have := (a9 (ZMod q) (tw q i)).1 (sch.obj X) m (by simpa using hm)
      exact Finite.of_subsingleton
    | succ N IH =>
      intro X p hp m hm
      rcases lt_or_eq_of_le (show m ≤ N by omega) with h | h
      · exact IH X p hp m h
      · subst h
        exact step _ IH _ X p hp le_rfl
  exact all (n.toNat + 1) X p inferInstance n (by omega)

end LateralTheory.E.E4

end
