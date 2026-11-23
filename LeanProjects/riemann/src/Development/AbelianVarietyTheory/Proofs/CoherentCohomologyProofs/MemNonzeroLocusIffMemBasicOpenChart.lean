import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem mem_nonzeroLocus_iff_mem_basicOpen_chart {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem mem_basicOpen_finset_prod_iff {Y : Scheme.{0}} {U : Y.Opens} {ι : Type} (f : ι → Γ(Y, U))
    (I : Finset ι) {x : Y} (hx : x ∈ U) :
    x ∈ Y.basicOpen (∏ i ∈ I, f i) ↔ ∀ i ∈ I, x ∈ Y.basicOpen (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hx
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_finset_biInf_opens_iff {Y : Scheme.{0}} {ι : Type} (D : ι → Y.Opens) (I : Finset ι)
    {x : Y} : x ∈ (⨅ i ∈ I, D i) ↔ ∀ i ∈ I, x ∈ D i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.forall_mem_insert, ← ih]
    rfl

theorem exists_prod_sec_nonzeroLocus : ∀ (Y : Scheme.{0}) (H : LB Y) (ι : Type) (s : ι → LB.Sec H) (I : Finset ι), H.IsLB → ∃ σ : LB.Sec (pw H (I.card : ℤ)), (∀ l : H.ι, σ.f l = ∏ i ∈ I, (s i).f l) ∧ nonzeroLocus σ = ⨅ i ∈ I, nonzeroLocus (s i) := by
  intro Y H ι s I hH
  let σ : LB.Sec (pw H (I.card : ℤ)) :=
    { f := fun l : H.ι => ∏ i ∈ I, (s i).f l
      compat := fun k l : H.ι => by
        change (Y.presheaf.map (homOfLE (inf_le_left : H.U k ⊓ H.U l ≤ H.U k)).op).hom
            (∏ i ∈ I, (s i).f k) = ((H.g k l ^ (I.card : ℤ) : Γ(Y, H.U k ⊓ H.U l)ˣ) :
              Γ(Y, H.U k ⊓ H.U l)) *
          (Y.presheaf.map (homOfLE (inf_le_right : H.U k ⊓ H.U l ≤ H.U l)).op).hom
            (∏ i ∈ I, (s i).f l)
        rw [map_prod, map_prod, zpow_natCast, Units.val_pow_eq_pow_val, ← Finset.prod_const,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (s i).compat k l }
  refine ⟨σ, fun _ => rfl, TopologicalSpace.Opens.ext (Set.ext fun x => ?_)⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (show x ∈ (⊤ : Y.Opens) from trivial))
  refine (mem_nonzeroLocus_iff_mem_basicOpen_chart σ l hl).trans
    (((mem_basicOpen_finset_prod_iff (fun i => (s i).f l) I hl).trans ?_).trans
      (mem_finset_biInf_opens_iff (fun i => nonzeroLocus (s i)) I).symm)
  exact forall₂_congr fun i _ => (mem_nonzeroLocus_iff_mem_basicOpen_chart (s i) l hl).symm

end GlobalTheory
