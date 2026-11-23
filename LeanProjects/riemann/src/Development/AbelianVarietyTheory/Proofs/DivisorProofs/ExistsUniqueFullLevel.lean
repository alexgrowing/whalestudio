import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIsoStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem weilIs_unitOn_unique {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  have hU : Subsingleton (Sp k) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  obtain ⟨p⟩ : Nonempty (Sp k) := by
    show Nonempty (PrimeSpectrum k); infer_instance
  have hp : ∀ V : (Over.mk x).left.Opens, p ∈ V → V = ⊤ := by
    intro V hV
    apply TopologicalSpace.Opens.ext
    ext y
    exact ⟨fun _ => trivial, fun _ => (Subsingleton.elim (α := Sp k) p y) ▸ hV⟩
  have H := GlobalTheory.ThetaGroupTest.weilIs_unique_of_local p hp hL h h'
  have hinj : Function.Injective (Units.map ((⊤ : (Over.mk x).left.Opens).ι.appTop.hom.toMonoidHom)) := by
    apply Units.map_injective
    haveI : IsIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤) := Scheme.Hom.isIso_app _ _ (by simp)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤)).1
  have H2 : unitOn c = unitOn c' := hinj H
  unfold unitOn at H2
  have hinj2 : Function.Injective (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) := by
    apply Units.map_injective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
  exact hinj2 H2

theorem exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by
  obtain ⟨-, I, hIA, hetaA, heta⟩ := o.geom k x β hx
  have hzA' : z ^ (l.M' / l.A) = I.ζ l.A := Units.ext (by rw [Units.val_pow_eq_pow_val, hzA, hIA])
  obtain ⟨ev, hev, hA, hM⟩ := GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso l I hz hzA'
  have hi : Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev :=
    ⟨fun a => (hA a).trans (hetaA a).symm, fun a ha => (hM a ha).trans (heta a ha).symm⟩
  refine ⟨ev, ⟨hev, hi⟩, ?_⟩
  rintro ev' ⟨h1, h2⟩
  have := GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels l (fun g g' c c' => weilIs_unitOn_unique o.t.G o.t.PP.isLB x _ g g' c c') hz
    hev hi h1 h2
  exact this.symm

end GlobalTheory.FullLevel
