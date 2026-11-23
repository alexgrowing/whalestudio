import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}}

abbrev OMm (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : Thick (Lm h q m) ⥤ ModuleCat.{0} O :=
  B.OM (Lm h q m) (Ideal.Quotient.mk _)

def redO (m : ℕ) : Om l O (m + 1) →+* Om l O m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ m.le_succ))

theorem dp_redO (h : OL l O) (m : ℕ) : IsDPMorphism (pdm h (m + 1)) (pdm h m) (redO m) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id O) _ Ideal.Quotient.mk_surjective (pdI_l l h.unit) (isPdm h _) (isPdm h _)
    (fun _ hx => hx) fun _ => rfl

def redN (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) :
    NMor (pdm h (m + 1)) q (κm l O (m + 1)) (pdm h m) q (κm l O m) (redO m) where
  hI := dp_redO h m
  u := 𝟙 X
  g := RingHom.id O
  hu := by simp
  hκ a r hr := by
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r at hr
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (redO m r)
    rw [Ideal.Quotient.eq] at hr ⊢
    have := (dp_redO h m).1 (Ideal.mem_map_of_mem (redO m) hr)
    rw [map_sub] at this
    exact this

def redMorO (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) :
    CH.Mor (OMm h q (m + 1)) (OMm h q m) (RingHom.id O) :=
  B.omMor ((redN h q m).mor l) (RingHom.id O) (fun _ => rfl)

def HSO (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (j : ℕ) : Sys.{1} O where
  M m := CH.H (OMm h q m) j
  r m := (redMorO h q m).pull j

variable {q : X ⟶ Spec (CommRingCat.of O)}

theorem lm_le_std (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m ≤ (stdI Q none ((l : O) ^ m)).S T := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine Ideal.mem_sup_right (Ideal.subset_span ?_)
  change (l : T.obj.B) ^ m = T.obj.i ((l : O) ^ m)
  rw [map_pow, map_natCast]

def gMor (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m) :
    CH.Mor (OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) where
  G := GF h Q m hQ
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x), by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        change Ideal.Quotient.factor (lm_le_std Q m T) (Ideal.Quotient.mk _ (T.obj.i c) * show GB (l := l) T.obj m from x) =
          Ideal.Quotient.mk _ (T.obj.i c) * Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x)
        rw [map_mul]
        rfl) }
  nat φ x := by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) _ m from x)
    refine Subtype.ext ?_
    change Ideal.Quotient.factor (lm_le_std Q m _) (gφ φ.hom m (show GB (l := l) _ m from x)) = _
    rw [← hy]
    rfl

end CrystallineSemistableComparison.Pb.Diso
