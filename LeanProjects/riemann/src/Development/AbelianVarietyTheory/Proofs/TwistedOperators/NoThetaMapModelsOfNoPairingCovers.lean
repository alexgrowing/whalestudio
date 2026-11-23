import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.NoLiftTransfer

theorem jm_mul_jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  unfold Jm Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply]

theorem conj_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ

  have h2 : Jm p q * Zᴴ * Jm p q + Z = 0 := by
    have h' := congrArg (fun X => Jm p q * X) h
    simpa [mul_add, ← mul_assoc, jm_mul_jm] using h'
  have h3 : (Jm p q * Zᴴ * Jm p q).trace + Z.trace = 0 := by rw [← Matrix.trace_add, h2, Matrix.trace_zero]
  rw [Matrix.trace_mul_comm, ← mul_assoc, jm_mul_jm, one_mul, Matrix.trace_conjTranspose] at h3
  rw [starRingEnd_apply]
  exact eq_neg_of_add_eq_zero_left h3

def invConj {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) : B →ₛₗ[starRingEnd ℂ] A where
  toFun := (Equiv.ofBijective u hb).symm
  map_add' x y := by
    apply hb.1
    rw [hadd]
    simp only [Equiv.ofBijective_apply_symm_apply]
  map_smul' z x := by
    apply hb.1
    rw [hsmul]
    simp only [Equiv.ofBijective_apply_symm_apply, Complex.conj_conj]

theorem invConj_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (u : A → B)
    (hb : Function.Bijective u) (hadd : ∀ x y, u (x + y) = u x + u y)
    (hsmul : ∀ (z : ℂ) x, u (z • x) = conj z • u x) (x : A) : invConj u hb hadd hsmul (u x) = x :=
  hb.1 ((Equiv.ofBijective u hb).apply_symm_apply (u x))

theorem noLift_of_pairNo : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  intro D V S M τ ι σ Z A pt κ p q T₁ R₁ a₁ l₁ c₁ b₁ e₁ u₁ hK hS hP

  have hsm : ∀ (z : ℂ) x, u₁ (z • x) = conj z • u₁ x := fun z x => by simpa [cjc] using hK.smul z x
  let w := invConj u₁ hK.bij hK.add hsm
  have hw_right : ∀ y, u₁ (w y) = y := fun y => (Equiv.ofBijective u₁ hK.bij).apply_symm_apply y
  have hw_left : ∀ v, w (u₁ v) = v := fun v => invConj_apply u₁ hK.bij hK.add hsm v
  intro U _ _ Q hQ

  let B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P => (Q (κ.symm P)).comp w
      map_add' := fun P P' => by ext x; simp
      map_smul' := fun z P => by ext x; simp }
  have hB : ∀ P x, B P x = Q (κ.symm P) (w x) := fun _ _ => rfl
  have hinv : PInv a₁ R₁ B := by
    intro Y hY P x
    set t : ℂ := (c₁ : ℂ) * Y.trace with ht_def

    have ht : conj t = -t := by rw [ht_def, map_mul, conj_trace hY, map_ratCast, mul_neg]
    have hX : phiFr (M.fr τ) b₁ e₁ Y ∈ lieAt V τ := by rw [← hK.lie]; exact ⟨Y, hY, rfl⟩
    have hpol : PolDer A pt (phiFr (M.fr τ) b₁ e₁ Y) (κ.symm P) (κ.symm (a₁ Y P + t • P)) :=
      (hS.der Y hY _ _).2 (by simp only [LinearEquiv.apply_symm_apply, ht_def])
    have hvec : VecDer M τ (phiFr (M.fr τ) b₁ e₁ Y) (w x) (w (R₁.HK.act Y x + t • x)) :=
      (hK.der Y hY _ _).2 (by simp only [hw_right, ht_def])
    have h0 := hQ _ hX _ _ _ _ hpol hvec
    have e1 : Q (κ.symm (a₁ Y P + t • P)) (w x) = Q (κ.symm (a₁ Y P)) (w x) + t • Q (κ.symm P) (w x) := by
      rw [map_add, map_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    have e2 : Q (κ.symm P) (w (R₁.HK.act Y x + t • x)) =
        Q (κ.symm P) (w (R₁.HK.act Y x)) - t • Q (κ.symm P) (w x) := by
      rw [map_add, map_add, map_smulₛₗ, ht, map_smul, neg_smul, sub_eq_add_neg]
    rw [e1, e2] at h0
    rw [hB, hB, ← h0]
    abel
  have hB0 : B = 0 := hP U B hinv
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  have h1 := congrArg (fun F : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U => F (κ P) (u₁ v)) hB0
  simpa [hB, hw_left] using h1

end GlobalTheory.ArchRec.NoLiftTransfer

end
