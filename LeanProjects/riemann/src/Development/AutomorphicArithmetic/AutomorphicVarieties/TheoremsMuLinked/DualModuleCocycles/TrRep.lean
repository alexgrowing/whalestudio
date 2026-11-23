import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.trRep :
    ∀ {O R G : Type} [CommRing O] [CommRing R] [Algebra O R] [Group G] {n : ℕ} (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O), 1 ≤ n → D.map x.toRingHom = GDet.ofRep ρ → (∀ y, (repR x ρ y).trace = x (D.tr y)) ∧ (∀ (r : R) y, repR x ρ (r • y) = x r • repR x ρ y) ∧ ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ y, t y = D.tr y := by
  intro O R G _ _ _ _ n D x ρ hn h
  refine ⟨fun y => ?_, fun r y => ?_, ?_⟩
  · have h1 := (((CA.d_gmap D).2.2.1 x.toRingHom y).2 1)
    rw [h] at h1
    have h2 := (CA.d_toDet (GDet.ofRep ρ) (MonoidAlgebra.mapRingHom G x.toRingHom y)).2.2.1
    rw [CA.d_toDet_ofRep.1 ρ, (CA.d_ofRep _ _ _).2.2.1 hn] at h2
    exact h2.trans h1
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
    | single g a =>
      rw [MonoidAlgebra.smul_single, repR_single, repR_single, smul_eq_mul, map_mul, mul_smul]
  · obtain ⟨t, ht⟩ := (CA.d_tr D.toDet).1 hn
    exact ⟨t, fun y => (ht y).trans (CA.d_toDet D y).2.2.1⟩
