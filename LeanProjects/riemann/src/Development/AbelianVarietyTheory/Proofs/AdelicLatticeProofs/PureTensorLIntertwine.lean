import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorL_intertwine {ι X : Type} (p : (X → ℂ) → Prop) (p0 : p 0) (padd : ∀ a b, p a → p b → p (a + b))
    (psmul : ∀ (c : ℂ) a, p a → p (c • a)) (A A' : ι → (X → ℂ) → (X → ℂ)) (Φ : Module.End ℂ (X → ℂ))
    (hA : ∀ i f, p f → p (A i f) ∧ Φ (A i f) = A' i (Φ f)) (f : X → ℂ) (hf : p f) (P : MvPolynomial ι ℂ) :
    p (pureTensorL A f P) ∧ Φ (pureTensorL A f P) = pureTensorL A' (Φ f) P := by
  have hl : ∀ l : List ι, p (l.foldr (fun i g => A i g) f) ∧
      Φ (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A' i g) (Φ f) := by
    intro l
    induction l with
    | nil => exact ⟨hf, rfl⟩
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih.2]
      exact hA i _ ih.1
  have hm : ∀ (B : ι → (X → ℂ) → (X → ℂ)) (g : X → ℂ) (k : ι →₀ ℕ) (c : ℂ),
      pureTensorL B g (MvPolynomial.monomial k c) = c • opPow B k g := by
    intro B g k c
    have e : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
  induction P using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [hm, hm, map_smul]
    exact ⟨psmul c _ (hl _).1, congrArg (c • ·) (hl _).2⟩
  | add P Q hP hQ =>
    rw [map_add, map_add, map_add, hP.2, hQ.2]
    exact ⟨padd _ _ hP.1 hQ.1, rfl⟩

theorem cplxO_move {m n : ℕ} {sS sS' G G' : Matrix (Fin n) (Fin n) ℂ} {sT sT' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (hS : sS' * G = G * sS) (hT : sT' * H = H * sT) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS' sT' (H * z * G') = H * cplxO sS sT z * G' := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have e : G' * sS' = sS * G' := by
    calc G' * sS' = G' * (sS' * G) * G' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]
      _ = sS * G' := by rw [hS, ← Matrix.mul_assoc, hG', Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc sT' * (H * z * G') * sS' = (sT' * H) * z * (G' * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, e]; simp only [Matrix.mul_assoc]

theorem unitMap_move {m n : ℕ} {B G G' : Matrix (Fin n) (Fin n) ℂ} {B' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (i : Fin m) (j : Fin n) : unitMap (G * B) (H * B') i j = H * unitMap B B' i j * G' := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hG]
  simp only [Matrix.mul_assoc]

theorem om_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' BS BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' BT BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ τ, BS' τ = compAt θ τ (mt S g) * BS τ) → (∀ τ, BT' τ = compAt θ τ (mt T h) * BT τ) → ∀ f, IsThetaFunO ψ S T f → ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧ om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS' sT' BS' BT' (om (g, h) f) P := by
  intro D ψ θ S T χS χT om hom hθ sS sS' BS BS' sT sT' BT BT' g h h1 h2 h3 h4 f hf P
  refine pureTensorL_intertwine (IsThetaFunO ψ S T) theta_zero (fun _ _ => theta_add) (fun c _ => theta_smul c) _ _
    (om (g, h)) (fun k f hf => ?_) f hf P
  obtain ⟨τ, i, j⟩ := k
  have hG := compAt_mt_mul_inv (θ := θ) τ g
  refine ⟨theta_smul _ (theta_sub (theta_dRho hθ hom.std τ _ hf) (theta_smul _ (theta_dRho hθ hom.std τ _ hf))), ?_⟩
  simp only [aPlusAll, aPlus, crea]
  rw [map_smul, map_sub, map_smul, om_dRho hom hθ g h τ _ hf, om_dRho hom hθ g h τ _ hf, h3, h4, unitMap_move hG,
    cplxO_move hG (h1 τ) (h2 τ)]

end GlobalTheory.OrientedHeis

end
