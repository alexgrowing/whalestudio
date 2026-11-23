import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifLinear

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem one_pG {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (1 : T ⟶ thickObj R I e G).left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A :=
  (congrArg CommaMorphism.left (TorusCoord.im_one g (T := T))).trans (Category.assoc _ _ _)

theorem comp_q_eq_iff {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) :
    y ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] ↔
      y.left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (1 : T ⟶ thickObj R I e G) ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] :=
    MonObj.one_comp _
  rw [← h1, ← one_pG g]
  refine ⟨fun h => congrArg CommaMorphism.left (TorusCoord.im_congr g h), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem comp_fstG_hom {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) {W : Scheme.{0}} (s : Spec (CommRingCat.of R) ⟶ W) :
    y.left ≫ (fstG I e G).left ≫ G.hom ≫ s = T.hom ≫ thick R I e ≫ s := by
  rw [← Over.w y, Category.assoc]
  exact congrArg (y.left ≫ ·) (pullback.condition_assoc s)

theorem map_pG (a : G ⟶ G) (b : D.P.A ⟶ D.P.A)
    (h : (Over.pullback (thick R I e)).map a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map b) :
    ((Over.pullback (thick R I e)).map a).left ≫ g.pG.left = g.pG.left ≫ b.left := by
  have A : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      pullback.fst D.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
  have h' := congrArg (fun f => f.left ≫ pullback.fst D.P.A.hom (thick R I e)) h
  simp only [Over.comp_left, Category.assoc, A] at h'
  exact h'.trans (Category.assoc _ _ _).symm

theorem appTop_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  rw [SplitTorus.charUnit_val]
  exact (SplitTorus.res_pullU_charUnit t χ _).symm.trans (congrArg Units.val (ht χ))

theorem identification_linear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (Φ : D'.toPre.P.A ≅ D.toPre.P.A), (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG → (∀ (a : O) (y : D'.toPre.X), xe (a • y) = a • xe y) ∧ ∀ a, ιD'.onB.act a ≫ Φ.hom = Φ.hom ≫ ιD.onB.act a := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' Φ hΦ xe hval O _ _ _ _ ιD ιD' ιA ιA' ιG hl hl'
  obtain ⟨hN, -, -, hc⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  refine ⟨?_, fun a => ?_⟩
  · have hI' : I ^ (0 + 1) ≠ ⊤ := fun h => by
      rw [zero_add, pow_one] at h
      rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hI
      exact bot_ne_top hI
    have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
    have : Nonempty (Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
    have k' := (comp_q_eq_iff (U'.gt 0) _).1 (U'.gt 0).isKernel.w
    have k : (U'.gt 0).i.left ≫ (U.gt 0).pG.left =
        (splitTorus _ D'.toPre.X).hom ≫ thick R I 0 ≫ eSec D.toPre.P.A := by
      refine Eq.trans ?_ (one_pG (U.gt 0))
      rw [← hΦ]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Φ.hom.left)
        (k'.trans (one_pG (U'.gt 0)).symm)).trans (Category.assoc _ _ _))
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ≫ (U.gt 0).i = (U'.gt 0).i :=
      ⟨_, (U.gt 0).isKernel.lift_fst _ _ ((comp_q_eq_iff (U.gt 0) _).2 k)⟩
    have hchar : ∀ x, τ.left.appTop.hom (charUnit _ D.toPre.X (xe x)).val =
        (charUnit _ D'.toPre.X x).val := fun x => by
      apply TopCat.Presheaf.section_ext (Scheme.sheaf _) ⊤
      intro z hz
      obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.toPre.P.L D.toPre.P.isLB z
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.toPre.P.L D'.toPre.P.isLB z
      have v := hval 0 _ (U'.gt 0).i.left z J J' hJ hJ' (k.trans (comp_fstG_hom _ _).symm)
        (k'.trans (comp_fstG_hom _ _).symm) x
      have v₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre 0 G (U.gt 0) _ τ 1 z J hJ
        (xe x)).1
      have v₂ := (TorusCoord.val_torus_point_and_translate R I D'.toPre 0 G (U'.gt 0) _ (𝟙 _) 1 z J'
        hJ' x).1
      rw [hτ] at v₁
      rw [Category.id_comp] at v₂
      have w := congrArg Units.val (v₁.symm.trans (v.trans v₂))
      rw [Geo.Tor.gm_val _ z ⊤ trivial, Geo.Tor.gm_val _ z ⊤ trivial] at w
      exact w
    intro a y
    obtain ⟨t, ht, hi⟩ := hl.i_lin 0 (star a)
    obtain ⟨t', ht', hi'⟩ := hl'.i_lin 0 (star a)
    have : Mono (U.gt 0).i :=
      (MorphismProperty.monomorphisms _).of_isPullback (U.gt 0).isKernel.flip
        (inferInstanceAs (Mono η[thickObj R I 0 D.toPre.P.A]))
    have ht₀ : t' ≫ τ = τ ≫ t := by
      rw [← cancel_mono (U.gt 0).i, Category.assoc, Category.assoc, ← hi, hτ, ← hi',
        ← Category.assoc, hτ]
    have h := congrArg (fun f => f.left.appTop.hom (charUnit _ D.toPre.X (xe y)).val) ht₀
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [hchar, appTop_of_torusEndOf ht, appTop_of_torusEndOf ht', star_star,
      ← xe.apply_symm_apply (a • xe y), hchar, SplitTorus.charUnit_val,
      SplitTorus.charUnit_val] at h
    rw [SplitTorus.chi_injective h, xe.apply_symm_apply]
  · have := D'.toPre.P.isAb.smooth
    have := D'.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D'.toPre.P.A).2 D.toPre.P.A _ _ fun n => ?_
    have := (U'.gt n).q_flat
    have := (U'.gt n).q_surj
    have := (U'.gt n).q_affine
    have e₁ := map_pG (U.gt n) _ _ (hl.q_lin n a)
    have e₂ := map_pG (U'.gt n) _ _ (hl'.q_lin n a)
    have hE : Epi (U'.gt n).q.left := inferInstance
    refine (cancel_epi (U'.gt n).q.left).1 ?_
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    change (U'.gt n).pG.left ≫ _ = (U'.gt n).pG.left ≫ _
    have e₃ := hΦ n
    generalize (U'.gt n).pG.left = p', (U.gt n).pG.left = p at e₁ e₂ e₃ ⊢
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc, e₃, ← e₁, ← e₃, ← e₂]
    exact Category.assoc _ _ _

end GlobalTheory.UnifLinear
