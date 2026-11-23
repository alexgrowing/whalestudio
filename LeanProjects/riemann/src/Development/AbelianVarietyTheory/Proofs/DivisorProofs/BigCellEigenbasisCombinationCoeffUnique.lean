import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_eigComb_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC S _ zw hzw x hx hUx σ a b w' ha hb
  subst hx
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hzw hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hvT : ∀ m, IsTanAtG TF.Y.t (zw ≫ toBase TF Z) (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hUx) (hv.1 m)
  let f : Fin (Dw.mult σ) → TanM (zw ≫ toBase TF Z) TF.Y.t.G := fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))
  have uniq : ∀ {w₁ w₂ : Sp (DualNumber S) ⟶ TF.Y.t.G.left} (cf : Fin (Dw.mult σ) → S),
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₁ →
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₂ → w₁ = w₂ := by
    intro w₁ w₂ cf h₁ h₂
    obtain ⟨u₁, hu₁, hw₁⟩ := h₁
    obtain ⟨u₂, hu₂, hw₂⟩ := h₂
    have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
    rw [← hw₁, ← hw₂, hu]
  have hsum : ∀ cf : Fin (Dw.mult σ) → S,
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf (tv (∑ j, cf j • f j)).left :=
    fun cf => (GlobalTheory.LieMet.isComb_iff f cf _).2 rfl
  have hab : ∑ j, a j • f j = ∑ j, b j • f j :=
    GlobalTheory.LieMet.tan_ext ((uniq a (hsum a) ha).trans (uniq b (hsum b) hb).symm)
  let V := TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxx σ
  let C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := (L σ * N σ).map (ev zw W hzw)
  have hV : ∀ i, V i = ∑ j, C i j • f j := fun i =>
    (GlobalTheory.LieMet.isComb_iff f _ _).1 (hcomb S zw hzw hUx hk hxx σ i)
  have hCdet : IsUnit C.det := by
    have hm : C = (L σ).map (ev zw W hzw) * (N σ).map (ev zw W hzw) := Matrix.map_mul
    rw [hm, Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => by
        show ev zw W hzw (L σ i j) = 0
        rw [hLz σ i j (OrderDual.toDual_lt_toDual.1 h), map_zero])]
      exact IsUnit.prod_univ_iff.2 fun i => (hLu σ i).map (ev zw W hzw)
    · rw [Matrix.det_of_upperTriangular (M := (N σ).map (ev zw W hzw)) (fun i j h => by
        show ev zw W hzw (N σ i j) = 0
        rw [hNz σ i j h, map_zero])]
      refine IsUnit.prod_univ_iff.2 fun i => ?_
      show IsUnit (ev zw W hzw (N σ i i))
      rw [hN1, map_one]; exact isUnit_one
  have hf' : ∀ j, f j = ∑ i, C⁻¹ j i • V i := fun j => by
    simp only [hV, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e2 : ∀ l, (∑ i, C⁻¹ j i * C i l) = (1 : Matrix _ _ S) j l := fun l => by
      rw [← Matrix.nonsing_inv_mul _ hCdet, Matrix.mul_apply]
    simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • f j = ∑ i, Matrix.vecMul cf C⁻¹ i • V i := fun cf => by
    simp only [hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  have hg : Matrix.vecMul a C⁻¹ = Matrix.vecMul b C⁻¹ := funext
    (Fintype.linearIndependent_iffₛ.1 (TF.X.F.linearIndependent_vecAt k _ hk hxx σ) _ _
      (by rw [← key, ← key, hab]))
  calc a = Matrix.vecMul (Matrix.vecMul a C⁻¹) C := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul b C⁻¹) C := by rw [hg]
    _ = b := by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]

end GlobalTheory.LogPole
