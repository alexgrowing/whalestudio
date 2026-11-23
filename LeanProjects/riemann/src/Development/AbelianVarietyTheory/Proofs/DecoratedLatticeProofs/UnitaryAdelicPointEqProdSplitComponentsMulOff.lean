import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocProd

variable {D : D7}

theorem mem_congGrp_entries (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := fun g hg =>
  (mem_congGrp_entries V J g).2 fun i j => h ((mem_congGrp_entries V I g).1 hg i j)

theorem idAt_le_idOff (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : idAt D P ≤ idOff D P' := by
  intro a ha
  have h2 := (Submodule.mem_inf.1 ha).2
  rw [Submodule.mem_iInf] at h2
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact h2 ⟨w, fun h' => h w h' hw⟩

theorem grpAt_le_grpOff' (V : HSp D) (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : grpAt V P ≤ grpOff V P' :=
  congGrp_mono V (idAt_le_idOff P P' h)

theorem mem_idOff_of_forall (P : Pl D → Prop) (a : AE D) (h : ∀ w, P w → a ∈ idOff D (· = w)) : a ∈ idOff D P := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at h ⊢
  intro w hw
  exact h w hw w rfl

theorem mem_grpOff_of_forall (V : HSp D) (P : Pl D → Prop) (g : GA D V) (h : ∀ w, P w → g ∈ grpOff V (· = w)) :
    g ∈ grpOff V P := by
  unfold grpOff
  rw [mem_congGrp_entries]
  intro i j
  exact mem_idOff_of_forall P _ fun w hw => (mem_congGrp_entries V _ g).1 (h w hw) i j

theorem map_list_prod_eq_one {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) :
    ∀ J : List ι, (∀ i ∈ J, φ (f i) = 1) → φ (J.map f).prod = 1
  | [], _ => by simp
  | a :: J, h => by
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      map_list_prod_eq_one φ f J fun i hi => h i (List.mem_cons_of_mem a hi), one_mul]

theorem map_list_prod_single {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) (j : ι)
    (h1 : ∀ i, i ≠ j → φ (f i) = 1) : ∀ J : List ι, J.Nodup → j ∈ J → φ (J.map f).prod = φ (f j)
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: J, hn, hj => by
    obtain ⟨ha, hn'⟩ := List.nodup_cons.1 hn
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases haj : a = j
    · subst haj
      rw [map_list_prod_eq_one φ f J fun i hi => h1 i fun e => ha (e ▸ hi), mul_one]
    · have hjJ : j ∈ J := by
        rcases List.mem_cons.1 hj with e | e
        · exact absurd e.symm haj
        · exact e
      rw [h1 a haj, one_mul, map_list_prod_single φ f j h1 J hn' hjJ]

theorem eq_prod_gl_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  intro D S k _ _ _ _ ι p n _ _ β hinj J hJ hall κ
  have hloc := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).1 κ
  have hcomm := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).2.1
  choose x hx y hy hxy using hloc
  have hfr := fun i => ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 (x i)).1 (hx i)
  choose g hg using hfr
  have hglAt : ∀ i, (β i).gl (g i) ∈ grpAt S (· = (p i).v) := fun i =>
    ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 _).2 ⟨g i, rfl⟩
  have key : ∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v) := by
    intro i
    rw [← hg i, hxy i, hcomm i (x i) (hx i) (y i) (hy i), mul_assoc, mul_inv_cancel, mul_one]
    exact hy i
  refine ⟨g, key, (J.map fun i => (β i).gl (g i)).prod⁻¹ * κ, ?_, (mul_inv_cancel_left _ _).symm⟩
  apply mem_grpOff_of_forall
  rintro w ⟨j, rfl⟩
  let φ := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idOff D (· = (p j).v)))).comp (matHom S)
  have hker : ∀ h, h ∈ grpOff S (· = (p j).v) ↔ φ h = 1 := fun h => MonoidHom.mem_ker
  have hκ : φ κ = φ ((β j).gl (g j)) := by
    have := (hker _).1 (key j)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have h1 : ∀ i, i ≠ j → φ ((β i).gl (g i)) = 1 := fun i hij =>
    (hker _).1 (grpAt_le_grpOff' S _ _ (fun w hw hw' => hij (hinj (hw.symm.trans hw'))) (hglAt i))
  rw [hker, map_mul, map_inv, map_list_prod_single φ (fun i => (β i).gl (g i)) j h1 J hJ (hall j), hκ, inv_mul_cancel]

end GlobalTheory.FinPl.LocProd

end
