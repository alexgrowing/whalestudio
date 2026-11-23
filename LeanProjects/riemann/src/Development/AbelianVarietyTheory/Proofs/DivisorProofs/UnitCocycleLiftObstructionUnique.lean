import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem mul_eq_zero_of_mem_map {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x x' : B} (hx : x ∈ I.map (algebraMap R B)) (hx' : x' ∈ I.map (algebraMap R B)) : x * x' = 0 := by
  have h := Ideal.mul_mem_mul hx hx'
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact (Submodule.mem_bot _).1 h

theorem isSig_unique {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
    [Algebra R₀ R₁] (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (hσ' : α.IsSig p σ')
    (y : R₁ ⊗[R₀] B₀) : σ' y = σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

theorem isObU_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  have hσσ : ∀ T y, σ' T y = σ T y := fun T y ↦ isSig_unique α (L.p T) (L.surj T) (σ T) (σ' T) (hσ T) (hσ' T) y
  have hy : ∀ (T T' : C) (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F.obj T', α.KerQ y ∧
      σ T' y = (v' T T' a : L.B T') * ((v T T' a)⁻¹ : (L.B T')ˣ) - 1 := by
    intro T T' a
    refine (sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
      (σ T') (hσ T')).2.2.2 _ ((L.ker T' _).1 ?_)
    rw [map_sub, map_mul, hv', ← hv, ← map_mul, Units.mul_inv, map_one, sub_self]
  choose y hyK hyσ using hy
  rw [H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -y T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L.smooth T''
  haveI : Module.Flat R (L.B T'') := Algebra.Smooth.flat R _
  have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
    (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b) (L.nat b)
    (σ T') (σ T'') (hσ T') (hσ T'')
  have bas := sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  have em : ∀ x, mp (ext R₁ F) b x = extHom R₁ (mp F b) x := fun _ ↦ rfl
  simp only [d1_apply, Pi.sub_apply, map_neg, em]
  rw [← sub_eq_zero]
  apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  · have k1 := nat.2 _ (hyK T T' a)
    have k2 := hyK T T'' (a ≫ b)
    have k3 := hyK T' T'' b
    have k4 := (hz T T' T'' a b).1
    have k5 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at k1 k2 k3 k4 k5 ⊢
    simp only [map_sub, map_add, map_neg, k1, k2, k3, k4, k5]
    simp
  ·
    have e1 := (hz T T' T'' a b).2
    have e2 := (hz' T T' T'' a b).2
    rw [hσσ] at e2
    set P := σ T'' (extHom R₁ (mp F b) (y T T' a)) with hP
    set Q := σ T'' (y T' T'' b) with hQ
    set Y := σ T'' (y T T'' (a ≫ b)) with hY
    set Z := σ T'' (z.1 T T' T'' a b) with hZ
    set Z' := σ T'' (z'.1 T T' T'' a b) with hZ'
    have va : (v' T T' a : L.B T') = (1 + σ T' (y T T' a)) * (v T T' a : L.B T') := by
      rw [hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vb : (v' T' T'' b : L.B T'') = (1 + Q) * (v T' T'' b : L.B T'') := by
      rw [hQ, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vab : (v' T T'' (a ≫ b) : L.B T'') = (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      rw [hY, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    rw [va, vb, vab, map_mul, map_add, map_one, nat.1] at e2
    rw [← hP] at e2
    have mem : ∀ x, σ T'' x ∈ I.map (algebraMap R (L.B T'')) := bas.1
    have sq : ∀ x x', σ T'' x * σ T'' x' = 0 := fun x x' ↦ mul_eq_zero_of_mem_map hI (mem x) (mem x')
    have hPQ : P * Q = 0 := sq _ _
    have hPZ : P * Z = 0 := sq _ _
    have hQZ : Q * Z = 0 := sq _ _
    have hZY : Z' * Y = 0 := sq _ _
    have hV : (v T T'' (a ≫ b) : L.B T'') * ((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) = 1 := Units.mul_inv _
    simp only [map_sub, map_add, map_neg]
    rw [← hP, ← hQ, ← hY, ← hZ, ← hZ']
    have E : (1 + P) * (1 + Q) * (1 + Z) * (v T T'' (a ≫ b) : L.B T'') =
        (1 + Z') * (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      linear_combination e2 - (1 + P) * (1 + Q) * e1
    linear_combination -(((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) : L.B T'') * E
      + ((1 + P) * (1 + Q) * (1 + Z) - (1 + Z') * (1 + Y)) * hV + (1 + Z) * hPQ + hPZ + hQZ - hZY

end GlobalTheory.LBObs
