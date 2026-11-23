import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilocalConjugateSameCharpoly
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf.KottLat

variable {p : ℕ} [Fact p.Prime]

theorem isIntV_add (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact Subring.add_mem _ (ha i) (hb i)

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact Subring.zero_mem _

theorem eventually_isIntV_map (G : HTGroup p) (y : AfP p ⊗[ℚ] G.C) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      IsIntV G v (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero]; exact isIntV_zero G v
  | tmul a c =>
    have h1 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
        AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := a.2
    have h2 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i,
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ := by
      simp only [Filter.eventually_all]; intro i; exact eventually_rat_mem_integers _
    filter_upwards [h1, h2] with v hv1 hv2 i
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsIntV, basV,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Subring.mul_mem _ hv1 (hv2 i)
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h1 h2
    rw [map_add]; exact isIntV_add G v h1 h2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

theorem conj_integral {A K : Type} [Ring A] [CommRing K] {n : ℕ} (R : Subring K)
    (Φ : Matrix (Fin n) (Fin n) K ≃+* A) (hfin : Set.Finite {I : Ideal R | I.IsMaximal})
    (Q : Polynomial R) (hQs : Q.Separable) (γ₀ : Aˣ) (hQm : Q.map R.subtype = (Φ.symm γ₀).charpoly)
    (hγ : ∀ i j, Φ.symm γ₀ i j ∈ R) (g : Aˣ) (hδ : ∀ i j, Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) i j ∈ R) :
    ∃ U : Aˣ, U * (g⁻¹ * γ₀ * g) = γ₀ * U ∧ (∀ i j, Φ.symm (U : A) i j ∈ R) ∧
      (∀ i j, Φ.symm ((U⁻¹ : Aˣ) : A) i j ∈ R) := by
  have lift : ∀ a : A, (∀ i j, Φ.symm a i j ∈ R) →
      ∃ M : Matrix (Fin n) (Fin n) R, M.map R.subtype = Φ.symm a :=
    fun a h => ⟨fun i j => ⟨_, h i j⟩, by ext i j; rfl⟩
  obtain ⟨Γ, hΓ⟩ := lift _ hγ
  obtain ⟨Δ, hΔ⟩ := lift _ hδ
  have hcΓ : Γ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΓ]
  have hcΔ : Δ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΔ]
    have e : Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) =
        (((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) * Φ.symm γ₀ *
        ((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul]; rfl
    rw [e, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  have hinj : Function.Injective (Polynomial.map R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have heq : Γ.charpoly = Δ.charpoly := hinj (hcΓ.trans hcΔ.symm)
  have hQ : Q = Γ.charpoly := hinj (hQm.trans hcΓ.symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.semilocal_conjugate_same_charpoly R hfin n Γ Δ heq (hQ ▸ hQs)
  let F : Matrix (Fin n) (Fin n) R →* A := (Φ.toRingHom.comp R.subtype.mapMatrix).toMonoidHom
  let U : Aˣ := Units.map F u
  have hUs : Φ.symm (U : A) = (u : Matrix (Fin n) (Fin n) R).map R.subtype := Φ.symm_apply_apply _
  have hUs' : Φ.symm ((U⁻¹ : Aˣ) : A) = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map R.subtype := by
    rw [show U⁻¹ = Units.map F u⁻¹ from (map_inv (Units.map F) u).symm]
    exact Φ.symm_apply_apply _
  refine ⟨U, Units.ext (Φ.symm.injective ?_), fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul U, Units.val_mul γ₀, map_mul, map_mul, hUs, ← hΔ, ← hΓ, ← Matrix.map_mul,
      ← Matrix.map_mul, hu]
  · rw [hUs, Matrix.map_apply]; exact (u : Matrix (Fin n) (Fin n) R) i j |>.2
  · rw [hUs', Matrix.map_apply]; exact ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

end GlobalTheory.OrbFinAf.KottLat
