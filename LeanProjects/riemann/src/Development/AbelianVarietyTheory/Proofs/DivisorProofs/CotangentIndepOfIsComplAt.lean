import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.TChart

theorem cotangent_indep_of_isComplAt : ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R] [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ (m : ℕ) (ι₀ : Fin m ↪ I), (∀ k, ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R) → ∀ c : Fin m → R, ∑ k, c k * ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) → ∀ k, c k ∈ maximalIdeal R := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc m ι₀ hX c hc k
  classical
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  haveI hflat : Module.Flat (MvPolynomial I W) R := hψ.2.2.1
  haveI := hloc
  have hsmul : ∀ (a : MvPolynomial I W) (r : R), a • r = ψ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let P : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ
  have hPm : P.map ψ = maximalIdeal R := hψ.2.2.2.1
  let δ : MvPolynomial I W → ResidueField R := fun f => residue R (ψ (MvPolynomial.pderiv (ι₀ k) f))
  have hπP : ∀ p ∈ P, residue R (ψ p) = 0 := fun p hp => (residue_eq_zero_iff _).2 hp
  have hδmul : ∀ a b, δ (a * b) = residue R (ψ a) * δ b + residue R (ψ b) * δ a := by
    intro a b; simp only [δ, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by intro a b; simp [δ]
  let K : Ideal (MvPolynomial I W) :=
    { carrier := {x | x ∈ P ∧ δ x = 0}
      add_mem' := fun {a b} ha hb => ⟨P.add_mem ha.1 hb.1, by rw [hδadd, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨P.zero_mem, by simp [δ]⟩
      smul_mem' := fun a x hx => ⟨P.mul_mem_left a hx.1, by
        rw [smul_eq_mul, hδmul, hx.2, hπP x hx.1, mul_zero, zero_mul, add_zero]⟩ }
  have hCW : (maximalIdeal W).map (MvPolynomial.C : W →+* MvPolynomial I W) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun w hw => ⟨?_, by simp [δ]⟩
    show ψ (MvPolynomial.C w) ∈ maximalIdeal R
    exact map_nonunit (ψ.comp MvPolynomial.C) w hw
  have hP2 : P ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun p hp q hq => ⟨P.mul_mem_left p hq, ?_⟩
    show δ (p * q) = 0
    rw [hδmul, hπP p hp, hπP q hq]; simp
  have hJ : maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) ≤ K.map ψ := by
    rw [← hPm, ← Ideal.map_pow, ← Ideal.map_map, ← Ideal.map_sup]
    exact Ideal.map_mono (sup_le hP2 hCW)
  let muT : TensorProduct (MvPolynomial I W) R P →ₗ[MvPolynomial I W] R :=
    (TensorProduct.rid (MvPolynomial I W) R).toLinearMap ∘ₗ (Submodule.subtype P).lTensor R
  have hmu : Function.Injective muT :=
    (TensorProduct.rid (MvPolynomial I W) R).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hmut : ∀ (r : R) (p : P), muT (r ⊗ₜ p) = ψ p * r := fun r p => by
    simp [muT, hsmul]
  let f : R →+ P →+ ResidueField R := AddMonoidHom.mk'
    (fun r => AddMonoidHom.mk' (fun p : P => residue R r * δ p) (by intro a b; simp [hδadd, mul_add]))
    (by intro a b; ext p; simp [add_mul])
  have hf : ∀ (a : MvPolynomial I W) (r : R) (p : P), f (a • r) p = f r (a • p) := by
    intro a r p
    simp only [f, AddMonoidHom.mk'_apply, hsmul, Submodule.coe_smul, smul_eq_mul, hδmul, hπP p p.2, map_mul]
    ring
  let L : TensorProduct (MvPolynomial I W) R P →+ ResidueField R := TensorProduct.liftAddHom f hf
  have hLt : ∀ (r : R) (p : P), L (r ⊗ₜ p) = residue R r * δ p := fun r p => by
    simp [L, f]
  have hspan : ∀ y ∈ K.map ψ, ∀ r : R, ∃ t, muT t = r * y ∧ L t = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      exact ⟨r ⊗ₜ ⟨j, hj.1⟩, by rw [hmut]; ring, by rw [hLt]; simp [hj.2]⟩
    | zero => intro r; exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨t₁, h₁, h₁'⟩ := hx r
      obtain ⟨t₂, h₂, h₂'⟩ := hy r
      exact ⟨t₁ + t₂, by rw [map_add, h₁, h₂]; ring, by rw [map_add, h₁', h₂', add_zero]⟩
    | smul a x _ hx =>
      intro r
      obtain ⟨t, h₁, h₂⟩ := hx (r * a)
      exact ⟨t, by rw [h₁, smul_eq_mul]; ring, h₂⟩
  have hX' : ∀ j, MvPolynomial.X (ι₀ j) ∈ P := hX
  let t₀ : TensorProduct (MvPolynomial I W) R P := ∑ j, c j ⊗ₜ ⟨MvPolynomial.X (ι₀ j), hX' j⟩
  have hmu0 : muT t₀ = ∑ j, c j * ψ (MvPolynomial.X (ι₀ j)) := by
    simp only [t₀, map_sum, hmut]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL₀ : L t₀ = residue R (c k) := by
    simp only [t₀, map_sum, hLt, δ, MvPolynomial.pderiv_X, Pi.single_apply, ι₀.injective.eq_iff]
    simp
  obtain ⟨t, ht₁, ht₂⟩ := hspan _ (hJ hc) 1
  have : t = t₀ := hmu (by rw [ht₁, _root_.one_mul, hmu0])
  rw [this, hL₀] at ht₂
  exact (residue_eq_zero_iff _).1 ht₂

end GlobalTheory.TChart
