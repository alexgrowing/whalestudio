import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsNv (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < s.val then r + j.val else r + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NLv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
      qminorOp (Q.EH k r) (rowsNv k r l s) (rowsNv k r l t) u f g

def FNv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NLv k r z z' l (Q.uC k r (Fin.last r) Y - 1) J)

end defs

def JDRvBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * ∏ a, c a) • NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g)

def JDRvTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J) c g

def JDRvStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FNv k r z z' Y J (Fin.last r) - Q.crd (Formalism.QuantumDeterminants.pbOp ⟨r - 1, by omega⟩) (FNv k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRvStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FNv k r z z' Y J ⟨l + 1, by omega⟩ -
          Q.crd (Formalism.QuantumDeterminants.pbOp ⟨l, by omega⟩) (FNv k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cbOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨l, by omega⟩)
            (FNv k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRvChainM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (Q.cmp (Q.vABs r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vABs r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRvConseq : Prop := JDRvTop → JDRvStepA → JDRvStepB → JDRvChainM

theorem jDRRadM_of_parts (hB : JDRvBeta) (hT : JDRvTop) (hA : JDRvStepA) (hS : JDRvStepB) (hC : JDRvConseq) :
    JDRRadM := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hβ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have h1 := hβ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  simp only [FNv, Q.resG] at h2
  simp only [Q.resG, rhvGrp, dMul, drF]
  rw [h1, smul_smul, smul_smul, show ∀ a b : ℂ, a * -σ⁻¹ * (σ * b) = -b * a from fun a b => by field_simp,
    ← smul_smul, h2, smul_neg, neg_smul, neg_neg]

end

end Formalism.FourierDecayAlt.P.CutMP
