import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WittSig

open Matrix
open scoped ComplexOrder

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, conjTranspose_apply]

theorem Jpq_conjTranspose (q p : ℕ) : (Formalism.UG.Jpq q p)ᴴ = Formalism.UG.Jpq q p := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem le_of_isotropic {n : Type} [Fintype n] [DecidableEq n] {q p r : ℕ} (J : Matrix n n ℂ)
    (hS : Formalism.UG.HasSignature J q p) (X Y : Matrix n (Fin r) ℂ) (hxx : Xᴴ * J * X = 0)
    (hxy : Xᴴ * J * Y = 1) : r ≤ p := by
  obtain ⟨e, P, hP⟩ := hS
  rw [cT_conj_eq] at hP
  set Q : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := (↑(P⁻¹) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) with hQdef
  have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := by simp [Q]
  have hJ : J.reindex e e = Qᴴ * Formalism.UG.Jpq q p * Q := by
    rw [← hP]
    have h1 : Qᴴ * (P : Matrix _ _ ℂ)ᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
    calc J.reindex e e = (Qᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e * ((P : Matrix _ _ ℂ) * Q) := by
          rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  set Z := Q * X.reindex e (Equiv.refl _) with hZdef
  set W := Q * Y.reindex e (Equiv.refl _) with hWdef
  have key : ∀ A B : Matrix n (Fin r) ℂ,
      (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) = Aᴴ * J * B := by
    intro A B
    have : (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) =
        (A.reindex e (Equiv.refl _))ᴴ * (Qᴴ * Formalism.UG.Jpq q p * Q) * B.reindex e (Equiv.refl _) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, ← hJ]
    ext i j
    simp [Matrix.mul_apply, Matrix.reindex_apply, conjTranspose_apply]
    rw [← Fintype.sum_sum_type (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k (e.symm x)) * B (e.symm x) j)]
    exact e.symm.sum_comp (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k x) * B x j)
  have hZZ : Zᴴ * Formalism.UG.Jpq q p * Z = 0 := by rw [hZdef, key, hxx]
  have hWZ : Wᴴ * Formalism.UG.Jpq q p * Z = 1 := by
    have h := key X Y
    rw [hxy, ← hZdef, ← hWdef] at h
    have h2 := congrArg conjTranspose h
    simpa [conjTranspose_mul, Jpq_conjTranspose, Matrix.mul_assoc] using h2
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) := (Z.submatrix Sum.inr id).mulVecLin
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set u := Z *ᵥ c with hu
    have hlow : ∀ i, u (Sum.inr i) = 0 := fun i => by
      have := congrFun hc i
      simpa [L, u, mulVec, dotProduct, submatrix] using this
    have h0 : star u ⬝ᵥ (Formalism.UG.Jpq q p *ᵥ u) = 0 := by
      have : star c ⬝ᵥ ((Zᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c) = 0 := by rw [hZZ]; simp
      rw [← this, hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have hup : (fun i => u (Sum.inl i)) = 0 := by
      rw [← dotProduct_star_self_eq_zero, ← h0]
      simp [Formalism.UG.Jpq, dotProduct, mulVec, Fintype.sum_sum_type, hlow, Matrix.one_apply]
    have hu0 : u = 0 := by
      funext x
      rcases x with i | i
      · exact congrFun hup i
      · exact hlow i
    calc c = (Wᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c := by rw [hWZ, one_mulVec]
      _ = (Wᴴ * Formalism.UG.Jpq q p) *ᵥ u := by rw [hu, mulVec_mulVec]
      _ = 0 := by rw [hu0, mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem wittIndex_le_neg {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}
    (hS : Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) {r : ℕ}
    {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf) : r ≤ p := by
  have hc := (GlobalTheory.AdelicU.isCMExt_host D).2.2.2 (tauE D τ)
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin M.rank) (Fin a) D.host.E)
      (B : Matrix (Fin M.rank) (Fin b) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * M.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D M τ * B.map (tauE D τ) := by
    intro a b A B
    rw [Matrix.map_mul, Matrix.map_mul, gramAt]
    congr 2
    ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hc]
  apply le_of_isotropic (gramAt D M τ) hS (Xf.map (tauE D τ)) (Yf.map (tauE D τ))
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittSig
