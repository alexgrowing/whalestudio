import Mathlib
import Formalism.PeriodIntegrals.FinOrdAd

noncomputable section

namespace PI.TensCpctDenWork

open NumberField IsDedekindDomain TensorProduct

section Coord

variable {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]

def coordR (φ : E →ₗ[F] F) : E ⊗[F] R →ₗ[F] R :=
  TensorProduct.lid F R ∘ₗ φ.rTensor R

theorem coordR_tmul (φ : E →ₗ[F] F) (e : E) (x : R) : coordR φ (e ⊗ₜ[F] x) = φ e • x := by
  simp [coordR]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem coordR_smul (φ : E →ₗ[F] F) (a : R) (t : E ⊗[F] R) :
    coordR φ (a • t) = a * coordR φ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e x =>
    rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, coordR_tmul, coordR_tmul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

def coordL (φ : E →ₗ[F] F) : E ⊗[F] R →ₗ[R] R where
  toFun := coordR φ
  map_add' := map_add _
  map_smul' a t := by rw [RingHom.id_apply, smul_eq_mul]; exact coordR_smul φ a t

theorem coordL_tmul (φ : E →ₗ[F] F) (e : E) (x : R) : coordL φ (e ⊗ₜ[F] x) = φ e • x :=
  coordR_tmul φ e x

end Coord

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ D : ℕ, 0 < D ∧ IsIntegral ℤ ((D : E) * x) := by
  obtain ⟨n, hn, -, hi⟩ := NumberField.exists_nat_le_mulHeight₁ x
  exact ⟨n, Nat.pos_of_ne_zero hn, hi⟩

end PI.TensCpctDenWork

open NumberField IsDedekindDomain TensorProduct PI.TensCpctDenWork in
theorem PI.tensCpctDen_of (hA : PI.AdCpctDen) : PI.TensCpctDen := by
  intro F E _ _ _ _ _
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  set b := Module.finBasis F E with hbdef
  have hcont : ∀ i, Continuous (coordL (R := FiniteAdeleRing (𝓞 F) F) (b.coord i)) := fun i =>
    IsModuleTopology.continuous_of_linearMap _
  choose Nf hNf0 hNf using fun i => hA F _ ((hC.image (hcont i)))
  choose Db hDb0 hDb using fun i => exists_nat_mul_isIntegral (b i)
  set N0 : ℕ := ∏ i, Nf i with hN0
  set D0 : ℕ := ∏ i, Db i with hD0
  have hN0pos : 0 < N0 := Finset.prod_pos fun i _ => hNf0 i
  have hD0pos : 0 < D0 := Finset.prod_pos fun i _ => hDb0 i
  refine ⟨N0 * D0, Nat.mul_pos hN0pos hD0pos, fun e he => ?_⟩
  have hφ : ∀ i, IsIntegral ℤ ((N0 : F) * b.coord i e) := by
    intro i
    have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.coord i e) ∈
        coordL (R := FiniteAdeleRing (𝓞 F) F) (b.coord i) '' C := by
      refine ⟨_, he, ?_⟩
      show coordL (b.coord i) ((e : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = _
      rw [coordL_tmul, Algebra.smul_def, mul_one]
    have h1 := hNf i (b.coord i e) hmem
    have hsplit : (N0 : F) = ((∏ j ∈ Finset.univ.erase i, Nf j : ℕ) : F) * (Nf i : F) := by
      rw [hN0, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      ring
    rw [hsplit, mul_assoc]
    exact (isIntegral_natCast _).mul h1
  have hb : ∀ i, IsIntegral ℤ ((D0 : E) * b i) := by
    intro i
    have hsplit : (D0 : E) = ((∏ j ∈ Finset.univ.erase i, Db j : ℕ) : E) * (Db i : E) := by
      rw [hD0, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      ring
    rw [hsplit, mul_assoc]
    exact (isIntegral_natCast _).mul (hDb i)
  have he_sum : ((N0 * D0 : ℕ) : E) * e =
      ∑ i, algebraMap F E ((N0 : F) * b.coord i e) * ((D0 : E) * b i) := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Module.Basis.coord_apply]
    push_cast
    ring
  rw [he_sum]
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (hb i)
  exact (hφ i).map (IsScalarTower.toAlgHom ℤ F E)
