import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem gdesc_ker {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (J : TwoSidedIdeal (MonoidAlgebra A G))
    (hJ : ∀ k, f k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J) (x : MonoidAlgebra A G)
    (hx : MonoidAlgebra.mapDomainAlgHom A A f x = 0) : x ∈ J := by
  have key : ∀ y : MonoidAlgebra A G,
      y - MonoidAlgebra.mapDomain (Function.surjInv hf) (MonoidAlgebra.mapDomainAlgHom A A f y) ∈ J := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g a =>
      have h1 := J.mul_mem_left (MonoidAlgebra.single (Function.surjInv hf (f g)) a) _
        (hJ ((Function.surjInv hf (f g))⁻¹ * g) (by simp [Function.surjInv_eq]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_inv_cancel_left, mul_one, mul_one] at h1
      simpa using h1
  simpa [hx] using key x

private theorem gdesc_toT {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G) :
    toT A G' B (MonoidAlgebra.mapDomainRingHom B f x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (MonoidAlgebra.mapDomainAlgHom A A f) (toT A G B x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g s => simp [toT_single]

theorem UpperTheory.V.Pa.gdet_desc :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G), Function.Surjective f → (∀ k, f k = 1 → D.Kills (MonoidAlgebra.single k 1 - 1)) → ∃ D' : GDet n A G', D'.comap f = D := by
  intro n A G G' _ _ _ f D hf hk
  have hs : Function.Surjective (MonoidAlgebra.mapDomainAlgHom A A f) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨g, rfl⟩ := hf g
      exact ⟨MonoidAlgebra.single g a, by simp⟩
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D.toDet (MonoidAlgebra.mapDomainAlgHom A A f) hs
    (gdesc_ker f hf _ fun k h => (UpperTheory.V.CA.d_ker _ _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hk k h)))
  refine ⟨GDet.ofDet D', ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  exact GDet.ext fun B _ _ x => congrArg (D'.D B) (gdesc_toT f B x)
