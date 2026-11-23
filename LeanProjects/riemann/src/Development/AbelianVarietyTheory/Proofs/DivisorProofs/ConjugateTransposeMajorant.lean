import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower

namespace GlobalTheory.Proof.ConjugateTransposeMajorant

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem csum_eq_coord (S : CSD K) (f g : S.Forms) :
    S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) = star (fun a => S.basis.repr f a) ⬝ᵥ S.H *ᵥ fun a => S.basis.repr g a := by
  have hf : ∀ c, (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr f]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hg : ∀ c, (g : S.Cl → S.V) c = ∑ a, S.basis.repr g a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr g]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have e : ∀ c, S.pair ((f : S.Cl → S.V) c) ((g : S.Cl → S.V) c) =
      ∑ a, ∑ b, star (S.basis.repr f a) * (S.pair ((S.basis a : S.Cl → S.V) c) ((S.basis b : S.Cl → S.V) c) *
        S.basis.repr g b) := by
    intro c
    rw [hf c, hg c, map_sum S.pair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  simp only [CSD.csum, CSD.H, e, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

omit [NumberField K] in
theorem map_conjTranspose_of_mem {m n : Type} (E : Matrix m n K) (hE : ∀ a k, E a k ∈ cmMax K) (σ : K →+* ℂ) :
    Eᴴ.map σ = (E.map σ)ᴴ := by
  ext i j
  exact hE j i σ

omit [NumberField K] [StarRing K] in
theorem map_mulVec' {m n : Type} [Fintype n] (E : Matrix m n K) (x : n → K) (σ : K →+* ℂ) :
    (fun a => σ ((E *ᵥ x) a)) = E.map σ *ᵥ fun k => σ (x k) := by
  funext a
  simp [Matrix.mulVec, dotProduct, map_sum]

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem repr_toF (x : Fin (B.dZ ℓ Z) → K) : (fun a => B.S.basis.repr (B.toF ℓ Z x) a) = B.fE ℓ Z *ᵥ x := by
  have : B.S.basis.equivFun (B.toF ℓ Z x) = B.fE ℓ Z *ᵥ x := by
    rw [BlockDat.fE, ← Matrix.mulVec_mulVec]
    exact B.S.basis.equivFun.apply_symm_apply _
  rw [← this]
  rfl

theorem HZ_eq : B.HZ ℓ Z = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H * B.fE ℓ Z) := by
  have : B.HV ℓ = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [BlockDat.HZ, this, BlockDat.fE, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem csumAt_toF (σ : K →+* ℂ) (x : Fin (B.dZ ℓ Z) → K) (u : B.S.Forms) :
    csumAt B.S σ (B.toF ℓ Z x) u = star (fun k => σ (x k)) ⬝ᵥ ((B.fE ℓ Z).map σ)ᴴ *ᵥ
      (B.S.H.map σ *ᵥ fun a => σ (B.S.basis.repr u a)) := by
  have h : (fun a => σ (B.S.basis.repr (B.toF ℓ Z x) a)) = (B.fE ℓ Z).map σ *ᵥ fun k => σ (x k) := by
    rw [← map_mulVec', ← repr_toF]
  unfold csumAt
  rw [h, Matrix.star_mulVec, Matrix.dotProduct_mulVec _ (((B.fE ℓ Z).map σ)ᴴ)]

end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_eq_csumAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms), IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → (∀ a k, B.fE ℓ Z a k ∈ cmMax K) → (∀ (v : InfinitePlace K) x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ * csumAt B.S v.embedding (B.toF ℓ Z x) (B.toF ℓ Z y)) ∧ ∀ u : B.S.Forms, (∀ x, B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (u : B.S.Cl → B.S.V) = 0) → ∀ (σ : K →+* ℂ) x, csumAt B.S σ (B.toF ℓ Z x) u = 0 := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z hH hE
  refine ⟨fun v x y => ?_, fun u hu σ x => ?_⟩
  · have h1 : ∀ w : Fin (B.dZ ℓ Z) → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K _) v w = fun k => v.embedding (w k) := by
      intro w; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    have h2 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y =
        star ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (x k)) ⬝ᵥ ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (y k)) := by
      simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1]
      rfl
    have h3 : (fun a => v.embedding (B.S.basis.repr (B.toF ℓ Z y) a)) =
        (B.fE ℓ Z).map v.embedding *ᵥ fun k => v.embedding (y k) := by
      rw [← map_mulVec', ← repr_toF]
    have h4 : (B.HZ ℓ Z).map v.embedding = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ •
        (((B.fE ℓ Z).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.fE ℓ Z).map v.embedding) := by
      rw [← map_conjTranspose_of_mem _ hE, ← Matrix.map_mul, ← Matrix.map_mul, HZ_eq]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    rw [h2, csumAt_toF, h3, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (hH.2 v).2, h4,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have h0 : (B.fE ℓ Z)ᴴ *ᵥ (B.S.H *ᵥ fun a => B.S.basis.repr u a) = 0 := by
      funext k
      have := hu (Pi.single k 1)
      rw [csum_eq_coord, repr_toF, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
      have e : star (Pi.single k (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single k 1 := by
        rw [Pi.star_single, star_one]
      rw [e, single_dotProduct, one_mul] at this
      exact this
    rw [csumAt_toF, ← map_mulVec', ← map_conjTranspose_of_mem _ hE, ← map_mulVec', h0]
    simp

end GlobalTheory.Proof.ConjugateTransposeMajorant

end
