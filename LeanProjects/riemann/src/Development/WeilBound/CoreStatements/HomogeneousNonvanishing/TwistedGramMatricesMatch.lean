import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CodimOneGramTwistAgreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjectiveStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwPhiF
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SpecStalkMap

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem genPt_specializes {R : CommRingCat} {Ω : Type} [Field Ω] (φ : R ⟶ CommRingCat.of Ω)
    (hφ : Function.Injective φ.hom) (q : Spec R) : genPt (Spec.map φ) ⤳ q := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) _ _).1
  intro a ha
  have e : ((Spec.map φ).base (IsLocalRing.closedPoint Ω)) =
      PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω) := rfl
  change a ∈ ((Spec.map φ).base (IsLocalRing.closedPoint Ω)).asIdeal at ha
  rw [e] at ha
  have h0 : φ.hom a = 0 := by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_iff_ne_zero.2 h)
  rw [show a = 0 from hφ (by rw [h0, map_zero])]
  exact q.asIdeal.zero_mem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f)
    (h : f = f') : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem specMap_fromSpecStalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X)
    (h : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ q) :
    Spec.map (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk q = ξ := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem hom_ext' {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    {W : Scheme.{0}} {k l : W ⟶ t'.G.left} (h0 : k ≫ m.φ = l ≫ m.φ) (h1 : k ≫ t'.G.hom = l ≫ t'.G.hom) : k = l :=
  m.cart.1.hom_ext h0 h1

theorem phi_w {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    m.φ ≫ t.G.hom = t'.G.hom ≫ f :=
  m.cart.1.w

theorem gramAt_iff_of_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ),
        M₁.GramAt t.PP.L z b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' h1 h2 _ _ _
    t tΩ k m mA' u u' M₁ φ hu hu' hn _ htie _ _ z hz r b Γ
  classical
  have hzq : A'.ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ centre z := A'.all _
  let p : Cpt A'.ξ := ⟨centre z, hzq⟩
  obtain ⟨hjm', hint'⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  obtain ⟨hjm, -⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨u'p, hu'p⟩ := hint'.1 hz
  obtain ⟨ΦF, ν, hΦ1, hΦ2, hν⟩ := PositivityTheory.UnitarySelfGeneration.tw_phiF E H D l Xo c Y.oF Y.m0 g Φ n hΦ
  have hxx : x' = x ≫ ΦF.hom :=
    pullback.hom_ext (by rw [Category.assoc, hΦ1, h1]) (by rw [Category.assoc, hΦ2, h2])
  have : IsDomain (A'.X.presheaf.stalk (centre z)) :=
    Function.Injective.isDomain (genMap A'.ξ p) (A'.tie.gen.inj p)
  let ξp : Sp Ω ⟶ Spec (A'.X.presheaf.stalk (centre z)) :=
    Spec.map (A'.X.presheaf.stalkSpecializes hzq ≫ Scheme.stalkClosedPointTo A'.ξ)
  have hξp : ξp ≫ A'.X.fromSpecStalk (centre z) = A'.ξ := specMap_fromSpecStalk A'.ξ _ hzq
  have hgen : ∀ q, genPt ξp ⤳ q := genPt_specializes _ (A'.tie.gen.inj p)
  have hξu' : ξp ≫ u'p = x' := by
    have := hjm'
    exact (cancel_mono Y'.j).1 (by rw [Category.assoc, hu'p, ← Category.assoc, hξp, hx'])
  obtain ⟨up, hup_def⟩ : ∃ up, up = u'p ≫ ΦF.inv := ⟨_, rfl⟩
  have hξup : ξp ≫ up = x := by
    rw [hup_def, ← Category.assoc, hξu', hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hup : up ≫ Y.j = A'.X.fromSpecStalk (centre z) ≫ e.hom ≫ A.f := by
    refine GlobalTheory.T.eq_of_eq_generic_projective O (Spec (A'.X.presheaf.stalk (centre z))) Y.X Y.s Ω ξp _ _ Y.proj hgen ?_
    rw [← Category.assoc, hξup, ← hx, reassoc_of% hξp, ← hξ, Category.assoc]
  obtain ⟨tp, π⟩ : ∃ tp : SAB H (Spec (A'.X.presheaf.stalk (centre z))), Nonempty (SABMap tp Y.oF.t up) := by
    obtain ⟨_, _, _, _, _, π, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt up Y.oF.t
    exact ⟨_, ⟨π⟩⟩
  obtain ⟨π⟩ := π
  obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m k
  obtain ⟨πY, hπY⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m π
  obtain ⟨πY', hπY'⟩ := exists_cast πY (show up ≫ (Y.jQ ≫ pullback.fst _ _) =
    A'.X.fromSpecStalk (centre z) ≫ (e.hom ≫ A.f) from hup)
  obtain ⟨mp, hmp⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ a πY'
  obtain ⟨m0c, hm0c⟩ := exists_cast Y.m0.toSABMap (Category.id_comp (pullback.fst _ _)).symm
  obtain ⟨w0, hw0⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y'.m0.toSABMap m0c
  obtain ⟨c1, hc1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν (twistMap π g)
  obtain ⟨c2, hc2⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ w0 c1
  obtain ⟨c3, hc3⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y'.m c2
  obtain ⟨c3', hc3'⟩ := exists_cast c3 (show ((up ≫ ΦF.hom) ≫ 𝟙 _) ≫ (Y'.jQ ≫ pullback.fst _ _) =
      A'.X.fromSpecStalk (centre z) ≫ A'.f by
    rw [Category.comp_id, hup_def]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hu'p)
  obtain ⟨mp', hmp'⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ A'.m c3'
  obtain ⟨νφ, hνφ⟩ : ∃ f : Y.oF.t.G.left ⟶ Y.oF.t.G.left, ν.φ = f := ⟨_, rfl⟩
  obtain ⟨nφ, hnφ⟩ : ∃ f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left, n.φ = f := ⟨_, rfl⟩
  obtain ⟨u'φ, hu'φ⟩ : ∃ f : tΩ.G.left ⟶ Y'.oF.t.G.left, u'.φ = f := ⟨_, rfl⟩
  obtain ⟨mAφ, hmAφ⟩ : ∃ f : tΩ.G.left ⟶ A'.t.G.left, mA'.φ = f := ⟨_, rfl⟩
  obtain ⟨c1φ, hc1φ⟩ : ∃ f : tp.G.left ⟶ Y.oF.t.G.left, c1.φ = f := ⟨_, rfl⟩
  obtain ⟨c2φ, hc2φ⟩ : ∃ f : tp.G.left ⟶ Y'.oF.t.G.left, c2.φ = f := ⟨_, rfl⟩
  obtain ⟨c3φ, hc3φ⟩ : ∃ f : tp.G.left ⟶ Y'.t.G.left, c3.φ = f := ⟨_, rfl⟩
  obtain ⟨c3'φ, hc3'φ⟩ : ∃ f : tp.G.left ⟶ Y'.t.G.left, c3'.φ = f := ⟨_, rfl⟩
  obtain ⟨mp'φ, hmp'φ⟩ : ∃ f : tp.G.left ⟶ A'.t.G.left, mp'.φ = f := ⟨_, rfl⟩
  have F1 : νφ ≫ Y.m0.toSABMap.φ = Y.m0.toSABMap.φ ≫ nφ := by subst hνφ hnφ; exact hν
  have F2 : u'φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ nφ := by subst hu'φ hnφ; exact hn
  have F3 : νφ ≫ Y.oF.t.G.hom = Y.oF.t.G.hom ≫ ΦF.hom := by subst hνφ; exact phi_w ν
  have F4 : u'φ ≫ Y'.oF.t.G.hom = tΩ.G.hom ≫ x' := by subst hu'φ; exact phi_w u'
  have F5 : mAφ ≫ A'.m.φ = u'φ ≫ Y'.m.φ := by subst hmAφ hu'φ; exact hu'
  have F7 : mAφ ≫ A'.t.G.hom = tΩ.G.hom ≫ A'.ξ := by subst hmAφ; exact phi_w mA'
  have F8 : c1φ = π.φ ≫ νφ := by subst hc1φ hνφ; exact hc1
  have F9 : c2φ = c1φ ≫ w0.φ := by subst hc2φ hc1φ; exact hc2
  have WorkedExample : c3φ = c2φ ≫ Y'.m.φ := by subst hc3φ hc2φ; exact hc3
  have LargeParameterEstimates : c3'φ = c3φ := by subst hc3'φ hc3φ; exact hc3'
  have F12 : c3'φ = mp'φ ≫ A'.m.φ := by subst hc3'φ hmp'φ; exact hmp'
  have InertPlaceConditions : mp'φ ≫ A'.t.G.hom = tp.G.hom ≫ A'.X.fromSpecStalk (centre z) := by subst hmp'φ; exact phi_w mp'
  have key : u.φ ≫ νφ ≫ w0.φ = u'φ := by
    refine hom_ext' Y'.m0.toSABMap ?_ ?_
    · simp only [Category.assoc]
      rw [← hw0, hm0c, F1, F2]
    · simp only [Category.assoc]
      rw [phi_w w0, Category.comp_id, F3, reassoc_of% (phi_w u), F4, hxx]
  refine GlobalTheory.T.codim_one_gram_twist_agree E H g A'.X Ω A'.ξ p t A'.t tp mp mp' A.Li M₁ (Flat.lieModelOfEquiv A'.M φ) ?_ z rfl r b Γ
  intro ev
  obtain ⟨w, hw1, hw2⟩ := htie ev
  have hsq : (w.left ≫ u.φ) ≫ Y.oF.t.G.hom = (w.left ≫ tΩ.G.hom ≫ ξp) ≫ up := by
    simp only [Category.assoc]
    rw [phi_w u, hξup]
  have hl1 := π.cart.1.lift_fst _ _ hsq
  have hl2 := π.cart.1.lift_snd _ _ hsq
  generalize π.cart.1.lift _ _ hsq = vv at hl1 hl2
  refine ⟨vv, ?_, ?_⟩
  · refine hom_ext' a ?_ ?_
    · simp only [Category.assoc]
      rw [← hmp, hπY', hπY, reassoc_of% hl1, ← hu, reassoc_of% hw1, ha]
    · simp only [Category.assoc]
      rw [phi_w mp, reassoc_of% hl2, hξp, ← hw1, Category.assoc, phi_w m]
  · have F6 : w.left ≫ mAφ = (A'.M.pt (φ ev)).left := by subst hmAφ; exact hw2
    show vv ≫ mp'.φ = (A'.M.pt (φ ev)).left
    rw [hmp'φ]
    refine hom_ext' A'.m ?_ ?_
    · simp only [Category.assoc]
      rw [← F12, LargeParameterEstimates, WorkedExample, F9, F8]
      simp only [Category.assoc]
      rw [reassoc_of% hl1, reassoc_of% key, ← F6, Category.assoc, F5]
    · simp only [Category.assoc]
      rw [InertPlaceConditions, reassoc_of% hl2, hξp, ← F6, Category.assoc, F7]

end GlobalTheory.CompanionTheory.Ar.SpecStalkMap

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem twisted_gram_matrices_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ),
        M₁.GramAt t.PP.L z b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ :=
  @GlobalTheory.CompanionTheory.Ar.SpecStalkMap.gramAt_iff_of_tied

end PositivityTheory.UnitarySelfGeneration
