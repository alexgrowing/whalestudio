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

namespace GlobalTheory.ChF

private theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]

private theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩

private def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)

theorem htd_dim_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _

end GlobalTheory.ChF
