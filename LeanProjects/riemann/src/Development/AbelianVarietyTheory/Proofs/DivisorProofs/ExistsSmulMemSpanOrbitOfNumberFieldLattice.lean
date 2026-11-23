import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIteratesOfLinearIndepende
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLinearIndependentOfIsFractionRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Matrix

namespace GlobalTheory.CyclicLattice

theorem exists_linearIndependent_mulVec_pow {R : Type} [CommRing R] [IsDomain R] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (hg : LinearIndependent R (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → R, LinearIndependent R (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let gK := g.map f
  let Φ : Matrix (Fin r) (Fin r) R →ₗ[R] Matrix (Fin r) (Fin r) K :=
    (Algebra.linearMap R K).mapMatrix
  have hΦ : Function.Injective Φ := fun a a' h => by
    ext i j
    exact hf (congrFun (congrFun h i) j)
  have hgK : LinearIndependent K (fun i : Fin r => gK ^ (i : ℕ)) := by
    have h1 := hg.map' Φ (LinearMap.ker_eq_bot.2 hΦ)
    have h2 : (Φ ∘ fun i : Fin r => g ^ (i : ℕ)) = fun i : Fin r => gK ^ (i : ℕ) := by
      funext i
      simp only [Function.comp_apply, gK, ← Matrix.map_pow]
      rfl
    rw [h2] at h1
    exact (LinearIndependent.iff_fractionRing R K).mp h1
  obtain ⟨w, hw⟩ :=
    GlobalTheory.CyclicVector.exists_linearIndependent_iterates_of_linearIndependent_pow gK hgK
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) w
  choose u hu using hs
  refine ⟨u, ?_⟩
  let Ψ : (Fin r → R) →ₗ[R] (Fin r → K) :=
    LinearMap.pi (fun i => (Algebra.linearMap R K).comp (LinearMap.proj i))
  have hΨ : Function.Injective Ψ := fun a a' h => funext fun i => hf (congrFun h i)
  have hfu : (f ∘ u) = (f s) • w := funext fun j => by
    simpa [Algebra.smul_def] using hu j
  have key : (Ψ ∘ fun i : Fin r => g ^ (i : ℕ) *ᵥ u) =
      fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w) := by
    funext i
    ext k
    have e1 := RingHom.map_mulVec f (g ^ (i : ℕ)) u k
    simp only [Function.comp_apply]
    change f ((g ^ (i : ℕ) *ᵥ u) k) = _
    rw [e1, Matrix.map_pow, hfu, Matrix.mulVec_smul]
  have hsK : f s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have h3 : LinearIndependent K (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) := by
    have := hw.units_smul (fun _ => Units.mk0 (f s) hsK)
    have e : (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) =
        (fun _ : Fin r => Units.mk0 (f s) hsK) • (fun i : Fin r => gK ^ (i : ℕ) *ᵥ w) := by
      funext i
      simp [Units.smul_def]
    rw [e]
    exact this
  have h4 := (LinearIndependent.iff_fractionRing R K).mpr h3
  rw [← key] at h4
  exact h4.of_comp

theorem exists_smul_mem_span_of_linearIndependent {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) (w : Fin r → M)
    (hw : LinearIndependent R w) :
    ∃ c : R, c ≠ 0 ∧ ∀ t : M, c • t ∈ Submodule.span R (Set.range w) := by
  classical
  let N : Matrix (Fin r) (Fin r) R := b.toMatrix w
  have hsum : ∀ z : Fin r → R, b.equivFun (∑ j, z j • w j) = N *ᵥ z := by
    intro z
    ext i
    simp [N, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hz0
    have : ∑ j, z j • w j = 0 := b.equivFun.injective (by rw [hsum, hz, map_zero])
    funext j
    exact Fintype.linearIndependent_iff.1 hw z this j
  refine ⟨N.det, hdet, fun t => ?_⟩
  have : N.det • t = ∑ j, (N.adjugate *ᵥ b.equivFun t) j • w j := by
    apply b.equivFun.injective
    rw [hsum, map_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_smul_mem_span_orbit : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  intro l _ T _ _ _ _ O F _ _ _ _ _ ρ hrank hind
  obtain ⟨α, hα⟩ := GlobalTheory.exists_pow_linearIndependent_of_isFractionRing O F
  set n := Module.finrank ℚ F with hn
  let b : Module.Basis (Fin n) ℤ_[l] T := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  set φ := ρ α with hφdef
  set g := LinearMap.toMatrix b b φ with hgdef
  have hpow : ∀ i : ℕ, LinearMap.toMatrix b b (φ ^ i) = g ^ i := fun i => by
    induction i with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]
  have hφ : LinearIndependent ℤ_[l] (fun i : Fin n => φ ^ (i : ℕ)) := by
    have := hind n (fun i => α ^ (i : ℕ)) hα
    simpa [φ, map_pow] using this
  have hg : LinearIndependent ℤ_[l] (fun i : Fin n => g ^ (i : ℕ)) := by
    have := hφ.map' (LinearMap.toMatrix b b).toLinearMap (LinearMap.toMatrix b b).ker
    simpa [Function.comp_def, hpow] using this
  obtain ⟨u, hu⟩ := exists_linearIndependent_mulVec_pow g hg
  set v : T := b.equivFun.symm u with hv
  have hw : ∀ i : ℕ, b.equivFun ((φ ^ i) v) = g ^ i *ᵥ u := by
    intro i
    have hu' : u = ⇑(b.repr v) := by
      rw [hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← hpow, hu', LinearMap.toMatrix_mulVec_repr, Module.Basis.equivFun_apply]
  have hli : LinearIndependent ℤ_[l] (fun i : Fin n => (φ ^ (i : ℕ)) v) := by
    have hfun : (fun i : Fin n => (φ ^ (i : ℕ)) v) =
        b.equivFun.symm.toLinearMap ∘ (fun i : Fin n => g ^ (i : ℕ) *ᵥ u) := by
      funext i
      apply b.equivFun.injective
      simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw]
    rw [hfun]
    exact hu.map' _ b.equivFun.symm.ker
  obtain ⟨c, hc, hct⟩ := exists_smul_mem_span_of_linearIndependent b _ hli
  refine ⟨v, c, hc, fun t => Submodule.span_mono ?_ (hct t)⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨α ^ (i : ℕ), by simp [φ, map_pow]⟩

end GlobalTheory.CyclicLattice
