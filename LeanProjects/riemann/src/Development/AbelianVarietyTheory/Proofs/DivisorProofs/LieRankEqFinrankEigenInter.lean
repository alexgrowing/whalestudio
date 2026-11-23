import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lieRank_eq_finrank_range_bC_inf_eig : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p) (Λ : Type) [CommRing Λ]
    [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ) (σ : Λ →+* O),
    D.lieRank σ = Module.finrank C ↥(LinearMap.range (bC C D) ⊓ eig C (actT D) σ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε Λ _ _ h D σ
  haveI : IsFractionRing O C := hv.isFractionRing
  have hinj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  let j : (Fin h → O) →ₗ[O] (Fin h → C) := (Algebra.linearMap O C).compLeft (Fin h)
  have hj : Function.Injective j := fun x y e => funext fun i => hinj (congrFun e i)
  have mv : ∀ (X : Matrix (Fin h) (Fin h) O) (z : Fin h → O),
      j (Matrix.toLin' X z) = Matrix.toLin' (X.map (algebraMap O C)) (j z) := by
    intro X z; funext i
    exact RingHom.map_mulVec (algebraMap O C) X z i
  have mb : ∀ z, j (D.bb z) = bC C D (j z) := fun z => mv _ z
  have mT : ∀ z, z ∈ D.Tsub σ ↔ j z ∈ eig C (actT D) σ := by
    intro z
    simp only [Datum.Tsub, eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    refine forall_congr' fun b => ?_
    rw [← mv, algebraMap_smul, ← map_smul, hj.eq_iff]
    rfl
  set U := LinearMap.range (bC C D) ⊓ eig C (actT D) σ with hU
  have hm : ∀ z : ↥(D.Lie ⊓ D.Tsub σ), j z ∈ U := by
    rintro ⟨_, ⟨z, rfl⟩, hz⟩
    exact ⟨⟨_, (mb z).symm⟩, (mT _).1 hz⟩
  let g : ↥(D.Lie ⊓ D.Tsub σ) →ₗ[O] U :=
    { toFun := fun z => ⟨j z, hm z⟩
      map_add' := fun x y => Subtype.ext (map_add j _ _)
      map_smul' := fun c x => Subtype.ext (map_smul j _ _) }
  haveI : IsLocalizedModule (nonZeroDivisors O) g :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have hs : algebraMap O C s ≠ 0 := (IsLocalization.map_units C s).ne_zero
        have e : ⇑(algebraMap O (Module.End O U) s) = fun z : U => algebraMap O C s • z := by
          funext z; simp
        rw [e]
        exact (MulAction.bijective (Units.mk0 _ hs))
      surj := by
        rintro ⟨_, ⟨w, rfl⟩, hw⟩
        obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
        choose z hz using hc
        have e : j z = (c : O) • w := funext hz
        have e2 : j (D.bb z) = (c : O) • bC C D w := by
          rw [mb, e, ← algebraMap_smul C, map_smul, algebraMap_smul]
        refine ⟨⟨⟨D.bb z, ⟨z, rfl⟩, (mT _).2 ?_⟩, c⟩, Subtype.ext e2.symm⟩
        rw [e2, ← algebraMap_smul C]
        exact Submodule.smul_mem _ _ hw
      exists_of_eq := fun e => ⟨1, by
        rw [Subtype.ext (hj (congrArg Subtype.val e))]⟩ }
  rw [Datum.lieRank, ← IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl,
    IsFractionRing.finrank_right_eq O C]

end GlobalTheory.DetInv
