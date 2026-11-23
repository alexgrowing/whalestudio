import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveDiscriminants.IsPrimCmap
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.TensorPrimeModuli.ExistsNsmulEqZeroOfTmul

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

namespace PrimeModuloFree

open LargePrimeDiscriminant

def zc (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (z : Chn (GL (Fin n) R) m) :
    ∀ t : ℕ, Chn (GL (Fin (lev l n t)) R) m
  | 0 => z
  | t + 1 => cmap (psi R l (lev l n t)) m (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m (zc R hl z t)

theorem le_lev {l : ℕ} (hl : 0 < l) (n : ℕ) : ∀ t, n ≤ lev l n t
  | 0 => le_rfl
  | t + 1 => (le_lev hl n t).trans (Nat.le_mul_of_pos_left _ hl)

theorem isCyc_zc (hC : SChain) (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n k : ℕ}
    {z : Chn (GL (Fin n) R) (k + 1)} (hz : IsCyc z) : ∀ t, IsCyc (zc R hl z t)
  | 0 => hz
  | t + 1 => by
    have h := isCyc_zc hC R hl hz t
    have h1 : bd _ k (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t)) = 0 := isCyc_cmap hC _ h
    have h2 : bd _ k (cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
      (zc R hl z t)) = 0 := isCyc_cmap hC _ h
    change bd (GL (Fin (l * lev l n t)) R) k (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
        (zc R hl z t)) = 0
    rw [map_sub, map_smul, h1, h2, smul_zero, sub_zero]

theorem wsys_zc (hC : SChain) {R : Type} [CommRing R] {k j : ℕ} {a : ∀ n : ℕ, Chn (GL (Fin n) R) (k + 1) →ₗ[ℝ] ℝ}
    (ha : WSys R k j a) {l : ℕ} (hl : 0 < l) {n : ℕ} {z : Chn (GL (Fin n) R) (k + 1)} (hz : IsCyc z) :
    ∀ t, a (lev l n t) (zc R hl z t) = (∏ i ∈ Finset.range t, ((l : ℝ) ^ j - (l : ℝ) ^ (i + 2))) * a n z
  | 0 => by
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    rfl
  | t + 1 => by
    have hc := isCyc_zc hC R hl hz t
    have ih := wsys_zc hC ha hl hz t
    rw [Finset.prod_range_succ]
    change a (l * lev l n t) (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
        (zc R hl z t)) = _
    rw [map_sub, map_smul, ha.2.2 l (lev l n t) _ hl hc, ha.2.1 _ _ _ _ hc, ih]
    simp only [smul_eq_mul]
    ring

theorem th_zc {k : ℕ} (θ : ∀ (G : Type) [Group G], LinearMap.ker (bd G k) →ₗ[ℝ] ℝ ⊗[ℤ] grpH G (k + 1))
    (hθn : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (z : LinearMap.ker (bd G k)) (z' : LinearMap.ker (bd H k)),
      z'.1 = cmap f (k + 1) z.1 → θ H z' = LinearMap.baseChange ℝ (grpHMap f (k + 1)).hom (θ G z))
    (hC : SChain) (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n : ℕ} (z : Chn (GL (Fin n) R) (k + 1))
    (hz : IsCyc z) (x : grpH (GL (Fin n) R) (k + 1)) (hx : θ _ ⟨z, hz⟩ = (1 : ℝ) ⊗ₜ x) :
    ∀ t, θ _ ⟨zc R hl z t, isCyc_zc hC R hl hz t⟩ = (1 : ℝ) ⊗ₜ zSeq R hl x t
  | 0 => hx
  | t + 1 => by
    have ih := th_zc θ hθn hC R hl z hz x hx t
    have hc := isCyc_zc hC R hl hz t
    have hs : lev l n t ≤ l * lev l n t := Nat.le_mul_of_pos_left (lev l n t) hl
    change θ (GL (Fin (l * lev l n t)) R) ⟨zc R hl z (t + 1), isCyc_zc hC R hl hz (t + 1)⟩ =
      (1 : ℝ) ⊗ₜ[ℤ] (zSeq R hl x (t + 1) : grpH (GL (Fin (l * lev l n t)) R) (k + 1))
    have e : (⟨zc R hl z (t + 1), isCyc_zc hC R hl hz (t + 1)⟩ : LinearMap.ker (bd (GL (Fin (l * lev l n t)) R) k)) =
        ⟨cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t), isCyc_cmap hC _ hc⟩ -
          ((l : ℝ) ^ (t + 2)) • ⟨cmap (stab R (lev l n t) (l * lev l n t) hs) (k + 1) (zc R hl z t),
            isCyc_cmap hC _ hc⟩ := rfl
    rw [e, map_sub, map_smul, hθn _ _ (psi R l (lev l n t)) ⟨_, hc⟩ _ rfl,
      hθn _ _ (stab R (lev l n t) (l * lev l n t) hs) ⟨_, hc⟩ _ rfl, ih,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    change _ = (1 : ℝ) ⊗ₜ ((grpHMap (psi R l (lev l n t)) (k + 1)).hom (zSeq R hl x t) -
      l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) hs) (k + 1)).hom (zSeq R hl x t))
    rw [TensorProduct.tmul_sub]
    congr 1
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact (map_nsmul (TensorProduct.mk ℤ ℝ _ 1) _ _).symm

end PrimeModuloFree

end PositivityTheory.KB

end
