import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Divisibility.ClassSumBridge
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lvl_consequence_one : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K), IsConjAt v0 → ∀ S : CSD K, S.Good 1 → (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) → ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r → S.ActRat r → ∀ (P : Subgroup G) (ψ : P →* Kˣ), (∀ i j, S.lvlH r P ψ i j ∈ cmMax K) ∧ (∀ v : InfinitePlace K, ((S.lvlH r P ψ).map v.embedding).PosDef) ∧ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ) ≤ S.lvlNab r P ψ := by
  intro K _ _ _ _ v0 hv0 S hS hH hpos G _ _ r hr hrat P ψ
  have hP := (Formalism.L2.DIV.level_idempotent_spec K v0 hv0 G P ψ).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ cmMax K :=
    Formalism.L2.DIV.image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (Formalism.L2.DIV.gaMat_rat S r hrat _ hP.rat)
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec :=
    (Formalism.L2.DIV.image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).1
  refine ⟨fun i j => ?_, fun v => ?_, ?_⟩
  · show ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) i j ∈ cmMax K
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine Subfield.mul_mem _ (Subfield.inv_mem _ (natCast_mem _ _)) (Subfield.sum_mem _ fun k _ => ?_)
    refine Subfield.mul_mem _ ?_ (hE k j)
    rw [Matrix.mul_apply]
    refine Subfield.sum_mem _ fun l _ => Subfield.mul_mem _ ?_ (hH l k)
    rw [Matrix.conjTranspose_apply]
    exact Formalism.L2.DIV.star_mem_cmMax (hE l i)
  · exact Formalism.L2.DIV.cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos v (hpos v)
  · intro y hy
    have h1 := Formalism.L2.DIV.level_dual_lattice_le K v0 hv0 S 1 hS (hpos v0) G r hr P ψ y hy
    rw [Nat.cast_one, one_smul] at h1
    show (S.lvlE r P ψ).mulVec y ∈ S.nabLat
    have h2 : (S.lvlE r P ψ).mulVec y ∈ S.delLat := h1
    have hle : S.delLat ≤ S.nabLat := by
      intro x hx
      simp only [CSD.delLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_comap, Submodule.mem_pi,
        Set.mem_univ, true_implies] at hx ⊢
      exact fun c => hS.del_le c (hx c)
    exact hle h2

end GlobalTheory
