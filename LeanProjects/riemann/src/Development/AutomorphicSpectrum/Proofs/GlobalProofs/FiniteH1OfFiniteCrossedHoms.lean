import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne

namespace GlobalTheory.CompanionTheory.Glob

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

noncomputable def oneCochainFun {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) : G → A.V :=
  fun g => c.1 (fun _ => g)

theorem oneCochainFun_injective {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) : Function.Injective (oneCochainFun A) := by
  intro c c' h
  apply Subtype.ext
  funext x
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hx]
  exact congrFun h (x 0)

theorem oneCochainFun_isLocallyConstant {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) :
    IsLocallyConstant (oneCochainFun A c) := by
  have hc : IsLocallyConstant (c : (Fin 1 → G) → A) := c.2
  exact hc.comp_continuous (continuous_pi fun _ => continuous_id)

theorem oneCochainFun_cocycle {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] (c : locallyConstantCochains A 1)
    (hc : (dLocallyConstant A 1).hom c = 0) (g h : G) :
    oneCochainFun A c (g * h) = oneCochainFun A c g + A.ρ g (oneCochainFun A c h) := by
  have key : A.ρ g ((c : (Fin 1 → G) → A) (fun i => ![g, h] i.succ)) +
      ∑ j : Fin 2, (-1 : k) ^ ((j : ℕ) + 1) •
        (c : (Fin 1 → G) → A) (Fin.contractNth j (· * ·) ![g, h]) = 0 := by
    have h1 := congrFun (congrArg Subtype.val hc) ![g, h]
    rw [dLocallyConstant_hom_apply] at h1
    exact h1
  rw [Fin.sum_univ_two] at key
  have e1 : (fun i : Fin 1 => ![g, h] i.succ) = fun _ => h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e2 : Fin.contractNth (0 : Fin 2) (· * ·) ![g, h] = fun _ => g * h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e3 : Fin.contractNth (1 : Fin 2) (· * ·) ![g, h] = fun _ => g := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have p0 : (-1 : k) ^ (((0 : Fin 2) : ℕ) + 1) = -1 := by
    show (-1 : k) ^ 1 = -1
    exact pow_one _
  have p1 : (-1 : k) ^ (((1 : Fin 2) : ℕ) + 1) = 1 := by
    show (-1 : k) ^ 2 = 1
    exact neg_one_sq
  rw [e1, e2, e3, p0, p1, neg_one_smul, one_smul] at key
  show (c : (Fin 1 → G) → A) (fun _ => g * h) =
    (c : (Fin 1 → G) → A) (fun _ => g) + A.ρ g ((c : (Fin 1 → G) → A) (fun _ => h))
  rw [← sub_eq_zero, ← neg_eq_zero, ← key]
  abel

theorem finite_cohomology_one_of_finite_cocycles :
    ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (A : Rep.{0} k G) [IsDiscreteRep A],
      {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite →
        Finite (cohomology A 1) := by
  intro k G _ _ _ _ A _ hfin
  have hd : ∀ z : (cochainsComplex A).cycles 1,
      (dLocallyConstant A 1).hom (((cochainsComplex A).iCycles 1).hom z) = 0 := by
    intro z
    have h1 : (cochainsComplex A).iCycles 1 ≫ (cochainsComplex A).d 1 (1 + 1) = 0 :=
      (cochainsComplex A).iCycles_d 1 (1 + 1)
    rw [cochainsComplex_d] at h1
    exact congrArg (fun φ => φ.hom z) h1
  have hinj : Function.Injective ((cochainsComplex A).iCycles 1).hom :=
    (ModuleCat.mono_iff_injective ((cochainsComplex A).iCycles 1)).1 inferInstance
  have hS : ∀ z : (cochainsComplex A).cycles 1,
      oneCochainFun A (((cochainsComplex A).iCycles 1).hom z) ∈
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)} :=
    fun z => ⟨oneCochainFun_isLocallyConstant A _, oneCochainFun_cocycle A _ (hd z)⟩
  have hFin : Finite ((cochainsComplex A).cycles 1) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun z => (⟨_, hS z⟩ :
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}))
      (fun z₁ z₂ hz => hinj (oneCochainFun_injective A (congrArg Subtype.val hz)))
  have hepi : Epi ((cochainsComplex A).homologyπ 1) := inferInstance
  have hsurj : Function.Surjective ((cochainsComplex A).homologyπ 1).hom :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex A).homologyπ 1)).1 hepi
  exact Finite.of_surjective _ hsurj

end GlobalTheory.CompanionTheory.Glob
