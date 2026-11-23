import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.TorusPull

open ReciprocityTheory.ChartRestriction.G.DVR

section One

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem mem_torus_iff {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) :
    (∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z) ↔
      z ≫ g.pG.left = z ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A := by
  have hb : (fstG I e G).left ≫ G.hom ≫ eSec D.P.A =
      ((Over.map (thick R I e)).obj (thickObj R I e G)).hom ≫ eSec D.P.A :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D.P.A) (Over.w (fstG I e G)))
  constructor
  · rintro ⟨τ, rfl⟩
    have c := ((CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w).trans (congrArg (g.i.left ≫ ·) hb)
    exact (Category.assoc _ _ _).trans ((congrArg (τ ≫ ·) c).trans (Category.assoc _ _ _).symm)
  · intro h
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (z ≫ (thickObj R I e G).hom)
    let a : FinalForm ⟶ thickObj R I e G := Over.homMk z rfl
    have k := (CharAgree.comp_q_eq_one_iff g a).2 (h.trans (congrArg (z ≫ ·) hb.symm))
    exact ⟨(g.isKernel.lift a (toUnit _) k).left,
      congrArg (fun q => q.left) (g.isKernel.lift_fst a (toUnit _) k)⟩

theorem val_torus {T : Scheme.{0}}
    (τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left) (χ : D.X) {y : T}
    {J : (T ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) :
    val (g.t χ) (τ ≫ g.i.left) y J = gm τ y ⊤ (charUnit _ D.X χ) := by
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (τ ≫ (splitTorus _ D.X).hom)
  let a : FinalForm ⟶ splitTorus _ D.X := Over.homMk τ rfl
  exact (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm a 1 y J hJ χ).1

end One

section Two

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))}
  {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)

include hp in

theorem unit_iff {Z : Scheme.{0}} (z : Z ⟶ T'.left) :
    z ≫ p'.left = z ≫ T'.hom ≫ eSec D'.P.A ↔ (z ≫ h) ≫ p.left = (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
  have b := TorusCoordPull.over_base hD p p' h hp
  have l : (z ≫ p'.left) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = (z ≫ h) ≫ p.left := by
    rw [Category.assoc, hp, Category.assoc]
  have r : (z ≫ T'.hom ≫ eSec D'.P.A) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (z ≫ h) ≫ T.hom ≫ eSec D.P.A := by
    rw [Category.assoc, Category.assoc, hD.he, Category.assoc, reassoc_of% b]
  refine ⟨fun H => l.symm.trans ((congrArg (· ≫ _) H).trans r), fun H => ?_⟩
  refine (pull_grp hD).1.hom_ext (l.trans (H.trans r.symm)) ?_
  have u : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  rw [Category.assoc, Category.assoc, Category.assoc, u, Over.w]
  exact congrArg (z ≫ ·) (Category.comp_id _).symm

end Two

theorem appTop_ext {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (r' : Z ⟶ Y') (a : Γ(Y, ⊤)ˣ) (b : Γ(Y', ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = gm r' z ⊤ b) : r.appTop.hom a.val = r'.appTop.hom b.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have := congrArg Units.val (h z)
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at this
  exact this

theorem torus_point_iff : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  intro R R' _ _ _ _ I I' φ D D' hD G _ _ G' _ _ e g g' h hp ht T z a
  have mem := (mem_torus_iff g' z).trans ((unit_iff hD g.pG g'.pG h hp z).trans (mem_torus_iff g (z ≫ h)).symm)
  have ch : ∀ τ' τ, τ' ≫ g'.i.left = z → τ ≫ g.i.left = z ≫ h → ∀ x,
      τ'.appTop.hom (charUnit _ D'.X x).val = τ.appTop.hom (charUnit _ D.X (hD.xe x)).val := by
    intro τ' τ h' h₀ x
    refine appTop_ext _ _ _ _ fun y => ?_
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB y
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB y
    obtain ⟨hψ, H⟩ := ht x
    have P := (maps_iff hD.w _ _ _ (g'.t x) (g.t (hD.xe x)) h _
      (GeneratorPullback.pullAlong_le D.P.L _ h _ _ hψ) (fun _ => rfl)).1 H
    let FinalForm : Over (Spec (CommRingCat.of R')) :=
      Over.mk (z ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom)
    let ρ : FinalForm ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk z rfl
    have hρ : ρ ≫ g'.pG = 1 := by
      refine Over.OverMorphism.ext (((mem_torus_iff g' z).1 ⟨τ', h'⟩).trans ?_)
      have k : (toUnit FinalForm).left = FinalForm.hom := (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eSec D'.P.A) k.symm)
    have v := TorusCoordPull.val_unit_pull hD g.pG g'.pG h hp P ρ hρ (y := y) hJ hJ'
    have v' := val_torus g' τ' x hJ'
    have v₀ := val_torus g τ (hD.xe x) hJ
    rw [h'] at v'
    rw [h₀] at v₀
    exact v'.symm.trans (v.symm.trans v₀)
  constructor
  · rintro ⟨τ', h', hx⟩
    obtain ⟨τ, h₀⟩ := mem.1 ⟨τ', h'⟩
    exact ⟨τ, h₀, fun x => (ch τ' τ h' h₀ x).symm.trans (hx x)⟩
  · rintro ⟨τ, h₀, hx⟩
    obtain ⟨τ', h'⟩ := mem.2 ⟨τ, h₀⟩
    exact ⟨τ', h', fun x => (ch τ' τ h' h₀ x).trans (hx x)⟩

end GlobalTheory.TorusPull
