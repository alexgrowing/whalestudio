import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreAbelianPartIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharAgree

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem comp_q_eq_one_iff (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a : Z ⟶ thickObj R I e G) :
    a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] ↔
      a.left ≫ g.pG.left = a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
  have h1 : (a ≫ g.q).left ≫ pullback.fst D.P.A.hom (thick R I e) = a.left ≫ g.pG.left :=
    Category.assoc _ _ _
  have h2 : (toUnit Z ≫ η[thickObj R I e D.P.A]).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
    have k1 := UnitValue.eSec_pullback_fst (thick R I e) D.P.A
    have k2 : (toUnit Z).left = a.left ≫ pullback.snd G.hom (thick R I e) :=
      ((Category.comp_id _).symm.trans (Over.w (toUnit Z))).trans (Over.w a).symm
    have k3 : pullback.fst G.hom (thick R I e) ≫ G.hom =
        pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg ((toUnit Z).left ≫ ·) k1).trans ?_)
    refine (congrArg (· ≫ thick R I e ≫ eSec D.P.A) k2).trans ((Category.assoc _ _ _).trans ?_)
    refine congrArg (a.left ≫ ·) ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ eSec D.P.A) k3.symm).trans (Category.assoc _ _ _)
  refine ⟨fun h => h1.symm.trans ((congrArg (fun φ => φ.left ≫ _) h).trans h2), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext (h1.trans (h.trans h2.symm)) ?_)
  exact (Over.w _).trans (Over.w _).symm

def Match (g : GtCoord I D e G) (g' : GtCoord I D' e G) (xe : D'.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
    r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
    ∀ x, val (g.t (xe x)) r z J = val (g'.t x) r z J'

omit [IsDomain R] in
theorem connected_thick [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) :
    ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint _) fun y _ => ?_⟩
    exact ⟨closure {y}, Set.subset_univ _,
      (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
      isPreconnected_singleton.closure⟩
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

variable [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
include hI

theorem exists_torus_iso (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ θ : splitTorus _ D'.X ≅ splitTorus _ D.X, IsMonHom θ.hom ∧ θ.hom ≫ g.i = g'.i := by
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have m' : Mono g'.i := ⟨fun a b h => g'.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have := g.i_hom
  have := g'.i_hom
  let u := g.isKernel.lift g'.i (toUnit _) (gtCoord_i_comp_q hI g g')
  let v := g'.isKernel.lift g.i (toUnit _) (gtCoord_i_comp_q hI g' g)
  have hu : u ≫ g.i = g'.i := g.isKernel.lift_fst _ _ _
  have hv : v ≫ g'.i = g.i := g'.isKernel.lift_fst _ _ _
  refine ⟨⟨u, v, ?_, ?_⟩, ⟨?_, ?_⟩, hu⟩
  · rw [← cancel_mono g'.i, Category.assoc, hv, hu, Category.id_comp]
  · rw [← cancel_mono g.i, Category.assoc, hu, hv, Category.id_comp]
  · change η ≫ u = η
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.one_hom, IsMonHom.one_hom]
  · change μ ≫ u = (u ⊗ₘ u) ≫ μ
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, hu]

theorem exists_match (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ xe : D'.X ≃+ D.X, Match g g' xe := by
  obtain ⟨θ, hθ, hi⟩ := exists_torus_iso hI g g'
  have := connected_thick hI e
  obtain ⟨xe, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.X D'.X θ hθ
  refine ⟨xe, fun Z r z J J' hJ hJ' _ h' x => ?_⟩
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let a : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g'.isKernel.lift a (toUnit _) ((comp_q_eq_one_iff g' a).2 h')
  have hτ : τ ≫ g'.i = a := g'.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ θ.hom) ≫ g.i = a := by rw [Category.assoc, hi, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ θ.hom) 1 z J hJ (xe x)).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D' e G g' FinalForm τ 1 z J' hJ' x).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))

theorem match_unique (g : GtCoord I D e G) (g' : GtCoord I D' e G) {f f' : D'.X → D.X}
    (h : Match g g' f) (h' : Match g g' f') : f = f' := by
  funext x
  have := connected_thick hI e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J' hJ' using fun ψ : (splitTorus _ D.X).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have c := (comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have c' := (comp_q_eq_one_iff g' g.i).1 (gtCoord_i_comp_q hI g' g)
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J J' hJ hJ' c c' x).trans
    (h' _ _ z J J' hJ hJ' c c' x).symm).trans (k _))

omit hI [IsLocalRing R] [IsNoetherianRing R] in

theorem match_down {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G) {f : D'.toPre.X → D.toPre.X}
    (h : Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))

end CharAgree

open CharAgree in

theorem unifPre_characterGroup_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G), ∃ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U'
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.toPre.X → D.toPre.X), Match (U.gt e) (U'.gt e) f →
      Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

end GlobalTheory
