import Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ClosedLift
import Development.EtaleCohomology.EtaleSheaves.LeafConeZeroPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.PointEvaluationWitness
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling LateralTheory.E.LeafPtWPf

theorem hrelZero : LeafHrelZero := by
  intro R _ F U E f hf n
  exact LateralTheory.E.E8.ExciseCut.LeafConeZero_of R ((chains R).map f) F (fun m => hf m) n

theorem eqv_of_iso' {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_square {R : Type} [CommRing R] {Z X Z0 X0 : Spc} (f : Z ⟶ X) (a : Z0 ⟶ Z) (g : Z0 ⟶ X0) (b : X0 ⟶ X)
    [IsIso g] (w : a ≫ f = g ≫ b) (F : Shv R) (ha : Eqv R a F) (hb : Eqv R b F) : Eqv R f F := fun n => by
  have h1 : Function.Bijective (pull R (g ≫ b) F n) := by
    have e : ⇑(pull R (g ≫ b) F n) = pull R g F n ∘ pull R b F n := funext (pull_comp R g b F n)
    rw [e]; exact (eqv_of_iso' g F n).comp (hb n)
  rw [← w] at h1
  have e : ⇑(pull R (a ≫ f) F n) = pull R a F n ∘ pull R f F n := funext (pull_comp R a f F n)
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' (ha n) _).1 h1

theorem unit_of {k A : Type} [Field k] [CommRing A] {B : Scheme.{0}} (toK : B ⟶ Sp k) (s : Sp A ⟶ B) (q : ℕ)
    (hq : IsUnit (q : k)) : IsUnit (q : A) := by
  have := hq.map (Spec.preimage (s ≫ toK)).hom
  simpa using this

section geo
variable {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B) {A : Type} [CommRing A] [IsLocalRing A]
  (s : Sp A ⟶ B)

abbrev rA (A : Type) [CommRing A] [IsLocalRing A] : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Sp A :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

def gF : pullback (prS p ι s ≫ pullback.snd p s) (rA A) ⟶ pullback (pullback.snd p s) (rA A) :=
  pullback.lift (pullback.fst _ _ ≫ prS p ι s) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])

variable {ι p s} in

def hF (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    pullback (pullback.snd p s) (rA A) ⟶ pullback (prS p ι s ≫ pullback.snd p s) (rA A) :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w)
      (by simp only [Category.assoc]; rw [hw, pullback.condition_assoc]))
    (pullback.snd _ _) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

theorem eZ : pullback.fst (prS p ι s ≫ pullback.snd p s) (rA A) ≫ pullback.snd (pullback.snd p s ≫ s) ι ≫ ι =
    pullback.snd (prS p ι s ≫ pullback.snd p s) (rA A) ≫ rA A ≫ s := by
  have c : pullback.snd (pullback.snd p s ≫ s) ι ≫ ι = prS p ι s ≫ pullback.snd p s ≫ s := pullback.condition.symm
  rw [c]
  have := pullback.condition_assoc (f := prS p ι s ≫ pullback.snd p s) (g := rA A) s
  simpa only [Category.assoc] using this

theorem gF_iso (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    IsIso (gF ι p s) := by
  refine ⟨⟨hF w hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · rw [← cancel_mono ι]
        simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        rw [hw, eZ]
    · simp only [hF, gF, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext <;> simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]
end geo

theorem proper_base_change_closed_fiber_strictly_henselian_equivalence_holds : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp A _ _ s hA w hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  have hqA := unit_of toK s q hq
  have := hp
  have : IsProper (pullback.snd p s) := inferInstance
  have : IsProper (prS p ι s ≫ pullback.snd p s) := inferInstance
  have h1 := hE2 q A hA hqA (pullback.snd p s) i
  have h2 := hE2 q A hA hqA (prS p ι s ≫ pullback.snd p s) i
  have := gF_iso ι p s w hw
  exact eqv_of_square (sch.map (prS p ι s)) (sch.map (pullback.fst _ (rA A))) (sch.map (gF ι p s))
    (sch.map (pullback.fst _ (rA A)))
    (by rw [← Functor.map_comp, ← Functor.map_comp, gF, pullback.lift_fst]) _ h2 h1

theorem LeafPtW_of : LateralTheory.E.SecondDegreeKilling.LeafPtW :=
  LateralTheory.E.LeafPtWPf.LeafPtW_of hrelZero closedLift proper_base_change_closed_fiber_strictly_henselian_equivalence_holds

end LateralTheory.E.PointEvaluationWitness
