import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w

namespace GlobalTheory.CompanionTheory.RedPull

theorem cls_eq_of_eq {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b)
    (ha : K.d n a = 0) (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem pull_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {F G : C ⥤ ModuleCat.{0} R} {F' G' : C' ⥤ ModuleCat.{0} R'}
    (a : CH.Mor F G (RingHom.id R)) (b : CH.Mor G G' σ) (c : CH.Mor F F' σ) (d : CH.Mor F' G' (RingHom.id R'))
    (j : ℕ) (h : ∀ x : CH.Cn F j, b.pullC j (a.pullC j x) = d.pullC j (c.pullC j x)) (z : CH.H F j) :
    b.pull j (a.pull j z) = d.pull j (c.pull j z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) j).1 z
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc a.hom x hx
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc b.hom _ h1
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc c.hom x hx
  have h4 := CrystallineSemistableComparison.CechClassBoundaries.cyc d.hom _ h3
  change b.hom.mapH j (a.hom.mapH j _) = d.hom.mapH j (c.hom.mapH j _)
  rw [CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' a.hom x hx h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' b.hom _ h1 h2,
    CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' c.hom x hx h3, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' d.hom _ h3 h4]
  exact cls_eq_of_eq (h x) h2 h4

theorem sq_toSq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} (mm : SMor Φ Φ' σ) (b : IdF Φ.A) (b' : IdF Φ'.A)
    (ha : mm.Le (IdF.top _) (IdF.top _)) (hb : mm.Le b b') (j : ℕ) (z : CH.H (CH.modF Φ.A) j) :
    (mm.sq ha hb).pull j ((toSq (IdF.top _) b fun _ => rfl).pull j z) =
      (toSq (IdF.top _) b' fun _ => rfl).pull j (mm.o.pull j z) := by
  refine pull_square _ _ _ _ j (fun x => ?_) z
  funext t
  exact Subtype.ext Ideal.quotientMap_mk

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := by
  intro O A A' _ _ _ _ _ I I' γ γ' X X' q q' σ m l s r n j z
  exact sq_toSq (nmS m l s) _ _ (fun _ _ _ => trivial) (nm_std m l s r n) j z

end GlobalTheory.CompanionTheory.RedPull
