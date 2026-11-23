import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTLiftLie

theorem exists_factor_of_sq_zero {C C₀ k : Type} [CommRing C] [CommRing C₀] [Field k] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (x : Sp k ⟶ Sp C) :
    ∃ ψ : C₀ →+* k, x = spMap ψ ≫ spMap π := by
  let φ : C →+* k := (Spec.preimage x).hom
  have hx : x = spMap φ := by
    show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
    simp
  have hker : RingHom.ker π ≤ RingHom.ker φ := by
    intro a ha
    have h2 : a * a ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha ha
    rw [hsq] at h2
    have h0 : a * a = 0 := by simpa using h2
    have : φ a * φ a = 0 := by rw [← map_mul, h0, map_zero]
    exact RingHom.mem_ker.2 (mul_self_eq_zero.1 this)
  have hc : (RingHom.liftOfSurjective π hπ ⟨φ, hker⟩).comp π = φ :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  generalize RingHom.liftOfSurjective π hπ ⟨φ, hker⟩ = ψ at hc
  refine ⟨ψ, ?_⟩
  rw [hx, ← hc]
  show Spec.map (CommRingCat.ofHom (ψ.comp π)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π)
  rw [← Spec.map_comp]
  rfl

theorem lieMult_of_sqZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h act hact k _ _ x β hx j
  obtain ⟨ψ, rfl⟩ := exists_factor_of_sq_zero π hπ hsq x
  have hact' : ∀ c, ((o₀.act.toF D).act c).left ≫ i = i ≫ ((act.toF D).act c).left :=
    fun c => hact _
  refine (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp C) (Sp C₀) A o₀.A (spMap π) i (act.toF D) (o₀.act.toF D)
    h hact' k (spMap ψ) (β.comp (b.t j)) D.m).1 ?_
  exact o₀.lieRank k (spMap ψ) β (by rw [← hx, Category.assoc]) j

end GlobalTheory.HTLiftLie
