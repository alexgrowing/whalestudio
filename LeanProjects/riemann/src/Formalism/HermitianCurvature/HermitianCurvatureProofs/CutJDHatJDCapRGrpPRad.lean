import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsN (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t)) •
      qminorOp (Q.EH k r) (rowsN k r l s) (rowsN k r l t) u f g

def FN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NL k r z z' l (Q.uC k r l Y) J)

end defs

def JDRBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * starRingEnd ℂ (∏ a, c a)) • NL k r z z' 0 (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)

def JDRTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 1 0 (Q.resG k r (Fin.last r) J) c g

def JDRStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FN k r z z' Y J (Fin.last r) + Q.crd (Formalism.QuantumDeterminants.pOp ⟨r - 1, by omega⟩) (FN k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.ciOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FN k r z z' Y J ⟨l + 1, by omega⟩ + Q.crd (Formalism.QuantumDeterminants.pOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.ciOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRChainP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 1 0 (Q.crd (Q.cmp (Q.vAB r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vAB r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRConseq : Prop := JDRTop → JDRStepA → JDRStepB → JDRChainP

theorem jDRRadP_of_parts (hB : JDRBeta) (hT : JDRTop) (hA : JDRStepA) (hS : JDRStepB) (hC : JDRConseq) :
    JDRRadP := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hBσ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hx
  have h1 := hBσ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := congrArg Neg.neg (hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hx)
  clear hBσ hCh hB hT hA hS hC
  simp only [Pi.neg_apply, neg_neg] at h2
  simp only [rhGrp, dMul, drbF, Pi.add_apply] at h2 ⊢
  rw [← h2]
  simp only [FN, Q.resG, h1]
  simp only [smul_smul, smul_neg, neg_smul]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP
