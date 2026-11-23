import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k
  simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]

set_option maxHeartbeats 2000000 in

theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
