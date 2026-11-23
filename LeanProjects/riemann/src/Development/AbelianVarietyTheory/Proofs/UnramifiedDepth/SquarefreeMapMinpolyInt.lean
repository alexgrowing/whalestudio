import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem squarefree_map_minpoly_int (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Finite ℤ OE] (a : OE) :
    Squarefree ((minpoly ℤ a).map (Int.castRingHom C)) := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : Irreducible (minpoly ℤ a) := minpoly.irreducible hi
  have h2 : Irreducible ((minpoly ℤ a).map (algebraMap ℤ ℚ)) :=
    ((minpoly.monic hi).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp h1
  have h3 := (h2.separable.map (f := algebraMap ℚ C)).squarefree
  rw [Polynomial.map_map] at h3
  have h4 : (algebraMap ℚ C).comp (algebraMap ℤ ℚ) = Int.castRingHom C := RingHom.ext_int _ _
  rwa [h4] at h3

private theorem aeval_map_minpoly_int (C : Type) [Field C] (OE : Type)
    [CommRing OE] (A : Type) [Ring A] [Algebra C A] (ρ : OE →+* A) (a : OE) :
    Polynomial.aeval (ρ a) ((minpoly ℤ a).map (Int.castRingHom C)) = 0 := by
  have h4 : Int.castRingHom C = algebraMap ℤ C := RingHom.ext_int _ _
  rw [h4, Polynomial.aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at this
  exact this

private theorem finite_ringHom_order (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    Finite (OE →+* C) := by
  classical
  let b := Module.Free.chooseBasis ℤ OE
  let p : OE → Polynomial C := fun a => (minpoly ℤ a).map (Int.castRingHom C)
  have hfin : ∀ a, Finite ((p a).rootSet C) := fun a => (Polynomial.rootSet_finite _ _).to_subtype
  let F : (OE →+* C) → ∀ i, (p (b i)).rootSet C := fun τ i =>
    ⟨τ (b i), Polynomial.mem_rootSet.mpr
      ⟨(squarefree_map_minpoly_int C OE (b i)).ne_zero, aeval_map_minpoly_int C OE C τ (b i)⟩⟩
  refine Finite.of_injective F fun τ σ h => ?_
  have : τ.toAddMonoidHom.toIntLinearMap = σ.toAddMonoidHom.toIntLinearMap :=
    b.ext fun i => congrArg Subtype.val (congrFun h i)
  exact RingHom.ext fun a => LinearMap.congr_fun this a

private theorem mem_iSup_of_eigenvector (C : Type) [Field C] (OE : Type) [CommRing OE]
    (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V) (χ : OE → C) (x : V)
    (hx : ∀ a, ρ a x = χ a • x) :
    x ∈ ⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a) := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hinj : Function.Injective fun c : C => c • x := smul_left_injective C h0
  let τ : OE →+* C :=
    { toFun := χ
      map_one' := hinj (by simp only [← hx, map_one, one_smul, Module.End.one_apply])
      map_mul' := fun a b => hinj (by
        simp only
        rw [← hx, map_mul, Module.End.mul_apply, hx b, map_smul, hx a, smul_smul, mul_comm])
      map_zero' := hinj (by simp only [← hx, map_zero, zero_smul, LinearMap.zero_apply])
      map_add' := fun a b => hinj (by
        simp only
        rw [← hx, map_add, LinearMap.add_apply, hx a, hx b, add_smul]) }
  refine Submodule.mem_iSup_of_mem τ ((Submodule.mem_iInf _).mpr fun a => ?_)
  exact Module.End.mem_eigenspace_iff.mpr (hx a)

theorem order_rep_diagonalisable : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], Finite (OE →+* C) ∧ ∀ (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V), iSupIndep (fun τ : OE →+* C => ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) ∧ (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) = ⊤ := by
  intro C _ _ _ OE _ _ _ _ _
  refine ⟨finite_ringHom_order C OE, fun V _ _ ρ => ⟨?_, ?_⟩⟩
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : OE => ρ a)
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
    have h2 := h.comp (f := fun τ : OE →+* C => (τ : OE → C)) DFunLike.coe_injective
    refine h2.mono fun τ => ?_
    exact iInf_mono fun a => (Module.End.genEigenspace (ρ a) (τ a)).mono le_top
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have hss : ∀ a, (ρ a).IsSemisimple := fun a =>
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero (squarefree_map_minpoly_int C OE a)
        (aeval_map_minpoly_int C OE _ ρ a)
    rw [eq_top_iff]
    rintro v -
    let W : Submodule C V := Submodule.span C (Set.range fun a : OE => ρ a v)
    have hW : ∀ a, W ∈ (ρ a).invtSubmodule := by
      intro a
      rw [Module.End.mem_invtSubmodule, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine Submodule.subset_span ⟨a * b, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    have hfin : FiniteDimensional C W := by
      let b := Module.Free.chooseBasis ℤ OE
      have hle : W ≤ Submodule.span C (Set.range fun i => ρ (b i) v) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
        simp only [SetLike.mem_coe]
        induction ha using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply]
          exact Submodule.add_mem _ hx hy
        | smul n x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply]
          exact zsmul_mem hx n
      have : FiniteDimensional C (Submodule.span C (Set.range fun i => ρ (b i) v)) :=
        FiniteDimensional.span_of_finite C (Set.finite_range _)
      exact Submodule.finiteDimensional_of_le hle
    let f : OE → Module.End C W := fun a => (ρ a).restrict (hW a)
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => LinearMap.restrict_commute (hcomm a b) (hW a) (hW b))
      (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
    have hv : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
    have hle : (⊤ : Submodule C W) ≤ Submodule.comap W.subtype
        (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) := by
      rw [← htop]
      refine iSup_le fun χ x hx => ?_
      refine mem_iSup_of_eigenvector C OE V ρ χ x fun a => ?_
      have h1 := (Submodule.mem_iInf _).mp hx a
      have h2 : (f a).IsSemisimple := (hss a).restrict (hW a)
      rw [h2.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
        Module.End.mem_eigenspace_iff] at h1
      exact congrArg Subtype.val h1
    exact hle (Submodule.mem_top (x := (⟨v, hv⟩ : W)))

end GlobalTheory
