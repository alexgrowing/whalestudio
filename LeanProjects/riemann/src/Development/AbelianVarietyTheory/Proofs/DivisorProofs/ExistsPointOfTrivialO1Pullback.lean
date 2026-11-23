import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.BdDim

theorem exists_basicOpen_eq_nonzeroLocus {W : Scheme.{0}} {A : LB W} (hA : A.IsLB) (h : LBIso A (LB.triv W))
    (t : A.Sec) : ∃ g : Γ(W, ⊤), W.basicOpen g = Out.nonzeroLocus t := by
  obtain ⟨u, hu⟩ := LBIso.symm h
  let a := DVR.secOfIso t hu (LB.isLB_triv W) hA
  refine ⟨a.f ⟨⟩, le_antisymm (fun y hy => ?_) ((DVR.nonzeroLocus_secOfIso u t hu _ hA).trans (iSup_le fun _ => le_rfl))⟩
  obtain ⟨b, hb⟩ := LB.mem_of_cover hA y
  have e2 := congrArg W.basicOpen (DVR.secOfIso_spec (u := u) t hu (LB.isLB_triv W) hA ⟨⟩ b)
  rw [DVR.isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hm : y ∈ ((LB.triv W).U ⟨⟩ ⊓ A.U b) ⊓ W.basicOpen (a.f ⟨⟩) := ⟨⟨trivial, hb⟩, hy⟩
  exact (DVR.mem_nonzeroLocus t y).2 ⟨b, (e2.le hm).2.2⟩

theorem isIso_appTop_of_isProper {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [IsIntegral X] [IsProper f] : IsIso f.appTop := by
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed K f
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hfin' : (f.appTop.hom.comp e.hom).Finite := hfin.comp (RingHom.Finite.of_surjective _ he.2)
  have hb : Function.Bijective (f.appTop.hom.comp e.hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) _ hfin'.to_isIntegral
  have hb' : Function.Bijective f.appTop.hom := (Function.Bijective.of_comp_iff _ he).1 hb
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb'

theorem exists_factor_of_isIso_appTop {W S U : Scheme.{0}} (s : W ⟶ S) [IsIso s.appTop] [IsAffine U] (l : W ⟶ U) :
    ∃ y : S ⟶ U, s ≫ y = l := by
  refine ⟨S.toSpecΓ ≫ Spec.map (inv s.appTop) ≫ Spec.map l.appTop ≫ U.isoSpec.inv, ?_⟩
  rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp,
    ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

theorem exists_point_of_trivial_O1 : ∀ (o k₀ : Type) [CommRing o] [Field k₀] [IsAlgClosed k₀] (b : o →+* k₀) (W : Scheme.{0}) (s : W ⟶ Sp k₀) (n : ℕ) (f : W ⟶ PSpace o n), IsIntegral W → IsProper s → f ≫ PSpace.str o n = s ≫ spMap b → LBIso ((ProjSpace.O1 o n).pull f) (LB.triv W) → ∃ y : Sp k₀ ⟶ PSpace o n, s ≫ y = f := by
  intro o k₀ _ _ _ b W s n f _ _ _ h
  have hF : IsField Γ(W, ⊤) := isField_of_universallyClosed k₀ s
  obtain ⟨x⟩ : Nonempty W := inferInstance
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart o n (f x)
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_nonzeroLocus (LB.isLB_pull (ProjSpace.O1_isLB o n) f) h
    (Cartier.secPull (ProjSpace.coord o n i) f)
  rw [Cartier.nonzeroLocus_secPull, ProjSpace.nonzeroLocus_coord] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hg
    exact hg.ge (show x ∈ f ⁻¹ᵁ (ProjSpace.O1 o n).U i from hi)
  have hu : IsUnit g := (hF.mul_inv_cancel hg0).elim fun c hc => IsUnit.of_mul_eq_one c hc
  rw [W.basicOpen_of_isUnit hu] at hg
  have hr : Set.range f ⊆ Set.range (ProjSpace.chart o n i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hg.le (Set.mem_univ c)
  have : IsAffine (ProjSpace.chart o n i) := ProjSpace.isAffineOpen_chart o n i
  have := isIso_appTop_of_isProper s
  obtain ⟨y, hy⟩ := exists_factor_of_isIso_appTop s (IsOpenImmersion.lift (ProjSpace.chart o n i).ι f hr)
  exact ⟨y ≫ (ProjSpace.chart o n i).ι, by rw [reassoc_of% hy, IsOpenImmersion.lift_fac]⟩

end GlobalTheory.BdDim
