import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem quot_finite {p : ℕ} [Fact p.Prime] (D : Datum p) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) (h𝔞 : 𝔞 ≠ ⊥) :
    Finite (D.La ⧸ wSub D 𝔞 r) := by
  have hr : 𝔞 ^ r ≠ ⊥ := pow_ne_zero r h𝔞
  have hN0 : Ideal.absNorm (𝔞 ^ r) ≠ 0 := fun h => hr (Ideal.absNorm_eq_zero_iff.mp h)
  have hNmem : ((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F) ∈ 𝔞 ^ r := Ideal.absNorm_mem _
  haveI hLa : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp D.finLa
  haveI : AddGroup.FG (D.La ⧸ wSub D 𝔞 r) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ (wSub D 𝔞 r)).toAddMonoidHom)
      (Submodule.mkQ_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (wSub D 𝔞 r) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Ideal.absNorm (𝔞 ^ r), Nat.pos_of_ne_zero hN0, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  refine ⟨((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F), hNmem, z, ?_⟩
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem UpperTheory.Gal.FiniteEtaleModels.grpFin_holds :
    GrpFin := by
  intro p _ D 𝔞 r h𝔞
  haveI hQ : Finite (D.La ⧸ wSub D 𝔞 r) := quot_finite D 𝔞 r h𝔞
  refine ⟨hQ, ?_⟩
  exact Finite.of_injective
    (fun e : (D.La ⧸ wSub D 𝔞 r) ≃ₗ[D.O] D.La ⧸ wSub D 𝔞 r => (e : D.La ⧸ wSub D 𝔞 r → D.La ⧸ wSub D 𝔞 r))
    (fun a b h => LinearEquiv.ext (congrFun h))
