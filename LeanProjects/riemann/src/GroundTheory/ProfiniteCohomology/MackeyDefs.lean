import Mathlib
import GroundTheory.ProfiniteCohomology.ShapiroDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

variable (U : Subgroup G) (ι : H →* G)

abbrev MackeyDoubleCoset : Type u :=
  DoubleCoset.Quotient (U : Set G) (ι.range : Set G)

def mackeySubgroup (x : G) : Subgroup H :=
  U.comap ((MulAut.conj x).toMonoidHom.comp ι)

theorem mem_mackeySubgroup (x : G) (h : H) :
    h ∈ mackeySubgroup U ι x ↔ x * ι h * x⁻¹ ∈ U :=
  Iff.rfl

def mackeyConj (x : G) : mackeySubgroup U ι x →* U :=
  ((MulAut.conj x).toMonoidHom.comp ι).subgroupComap U

@[simp]
theorem mackeyConj_apply_coe (x : G) (h : mackeySubgroup U ι x) :
    ((mackeyConj U ι x h : U) : G) = x * ι h * x⁻¹ :=
  rfl

variable (N : Rep.{u} k U)

abbrev mackeyRep (x : G) : Rep.{u} k (mackeySubgroup U ι x) :=
  Rep.res (mackeyConj U ι x) N

noncomputable abbrev mackeySummand (x : G) : Rep.{u} k H :=
  Rep.coind (mackeySubgroup U ι x).subtype (mackeyRep U ι N x)

theorem mackeyProj_mem (x : G) (f : Rep.coind U.subtype N) :
    (fun h : H => f.1 (x * ι h)) ∈
      Representation.coindV (mackeySubgroup U ι x).subtype (mackeyRep U ι N x).ρ := by
  intro h' h
  have e : x * ι ((mackeySubgroup U ι x).subtype h' * h) =
      U.subtype (mackeyConj U ι x h') * (x * ι h) := by
    simp [mul_assoc]
  change f.1 (x * ι ((mackeySubgroup U ι x).subtype h' * h)) = N.ρ (mackeyConj U ι x h') _
  rw [e, f.2]

noncomputable def mackeyProj (x : G) :
    Rep.res ι (Rep.coind U.subtype N) ⟶ mackeySummand U ι N x :=
  Rep.ofHom ⟨{
      toFun := fun f => ⟨fun h => f.1 (x * ι h), mackeyProj_mem U ι N x f⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl },
    fun h₀ => by
      ext f h
      change f.1 (x * ι h * ι h₀) = f.1 (x * ι (h * h₀))
      rw [map_mul, mul_assoc]⟩

@[simp]
theorem mackeyProj_hom_apply (x : G) (f : Rep.coind U.subtype N) (h : H) :
    ((mackeyProj U ι N x).hom f).1 h = f.1 (x * ι h) :=
  rfl

theorem finite_mackeyDoubleCoset [U.FiniteIndex] : Finite (MackeyDoubleCoset U ι) := by
  have : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  refine Finite.of_surjective (fun c : G ⧸ U => Quotient.liftOn' c
    (fun y => DoubleCoset.mk U ι.range y⁻¹) fun a b hab => ?_) ?_
  · rw [QuotientGroup.leftRel_apply] at hab
    rw [DoubleCoset.eq]
    exact ⟨(a⁻¹ * b)⁻¹, U.inv_mem hab, 1, ι.range.one_mem, by group⟩
  · intro d
    induction d using Quotient.inductionOn' with
    | h y => exact ⟨(y⁻¹ : G), by simp⟩

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  (V : OpenSubgroup G) {ι} (hι : Continuous ι)

include hι in

theorem isOpen_mackeySubgroup (x : G) : IsOpen (mackeySubgroup (V : Subgroup G) ι x : Set H) :=
  V.isOpen.preimage ((continuous_const.mul hι).mul continuous_const)

def mackeyOpenSubgroup (x : G) : OpenSubgroup H :=
  ⟨mackeySubgroup (V : Subgroup G) ι x, isOpen_mackeySubgroup V hι x⟩

@[simp]
theorem coe_mackeyOpenSubgroup (x : G) :
    (mackeyOpenSubgroup V hι x : Subgroup H) = mackeySubgroup (V : Subgroup G) ι x :=
  rfl

include hι in

theorem continuous_mackeyConj (x : G) : Continuous (mackeyConj (V : Subgroup G) ι x) :=
  Continuous.subtype_mk ((continuous_const.mul (hι.comp continuous_subtype_val)).mul
    continuous_const) _

include hι in

theorem isDiscreteRep_mackeyRep (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N] (x : G) :
    IsDiscreteRep (mackeyRep (V : Subgroup G) ι N x) :=
  IsDiscreteRep.res (continuous_mackeyConj V hι x) N

end Topology

end GroundTheory.ProfCoh
