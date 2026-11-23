import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Obs.TrivAug

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem mul_eq_of_map_eq {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hk : RingHom.ker π = I)
    {a b : R} (h : π a = π b) (i : I) : a * (i : R) = b * i := by
  have h1 : a - b ∈ I := hk ▸ (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]))
  have h2 : (a - b) * (i : R) ∈ I ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul h1 i.2
  rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at h2
  exact h2

def smulI (I : Ideal R) {π : R →+* R₀} (hπ : Function.Surjective π) : SMul R₀ I :=
  ⟨fun r i => ⟨Function.surjInv hπ r * i, I.mul_mem_left _ i.2⟩⟩

def modI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ I :=
  @Function.Surjective.moduleLeft R R₀ I _ _ _ _ (smulI I hπ) π hπ (fun c x => by
    apply Subtype.ext
    show Function.surjInv hπ (π c) * (x : R) = c * x
    exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π c)) x)

def modOpI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ᵐᵒᵖ I :=
  letI := modI hI hπ hk
  Module.compHom I (RingEquiv.toOpposite R₀).symm.toRingHom

end GlobalTheory.Obs.TrivAug
end

open GlobalTheory.Obs.TrivAug in
theorem GlobalTheory.Obs.exists_aug : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  intro R R₀ _ _ I hI π hπ hk
  letI : Module R₀ I := modI hI hπ hk
  letI : Module R₀ᵐᵒᵖ I := modOpI hI hπ hk
  haveI : IsCentralScalar R₀ I := ⟨fun r m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (MulOpposite.op r)) * (m : R) = Function.surjInv hπ r * m
    rfl⟩
  haveI : IsScalarTower R₀ R₀ᵐᵒᵖ I := ⟨fun r s m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (r • s)) * (m : R) = Function.surjInv hπ r * (Function.surjInv hπ (MulOpposite.unop s) * m)
    rw [← _root_.mul_assoc]
    refine mul_eq_of_map_eq hI hk ?_ m
    simp [Function.surjInv_eq hπ, smul_eq_mul, mul_comm]⟩
  refine ⟨TrivSqZeroExt R₀ I, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
  { q := TrivSqZeroExt.fstHom R₀ R₀ I
    k := { toFun := fun y => (y.snd : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
    mem := fun y => y.snd.2
    smul := fun r y => by
      show Function.surjInv hπ (π r) * (y.snd : R) = r * y.snd
      exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π r)) _
    one := rfl
    sq := fun y y' h h' => by
      have h0 : y.fst = 0 := h
      have h0' : y'.fst = 0 := h'
      ext
      · simp [h0]
      · simp [h0, h0']
    inj := fun y h h' => by
      have h0 : y.fst = 0 := h
      ext
      · exact h0
      · have h1 : (y.snd : R) = 0 := h'
        rw [h1]; rfl
    surj := fun i hi => ⟨TrivSqZeroExt.inr ⟨i, hi⟩, rfl, rfl⟩ }
