import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLiftOfRingAutomorphismStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃+* Ainf p O :=
  RingEquiv.ofRingHom (WittVector.map (G : PreTilt O p →+* PreTilt O p))
    (WittVector.map (G.symm : PreTilt O p →+* PreTilt O p))
    (by ext x n; simp [WittVector.map_coeff])
    (by ext x n; simp [WittVector.map_coeff])

theorem wittEquiv_apply (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G a = WittVector.map (G : PreTilt O p →+* PreTilt O p) a := rfl

theorem wittEquiv_ofPadic (G : PreTilt O p ≃+* PreTilt O p) (x : ℤ_[p]) :
    wittEquiv G (ofPadic p O x) = ofPadic p O x := by
  rw [wittEquiv_apply, ofPadic, RingHom.comp_apply]
  generalize (WittVector.equiv p).symm.toRingHom x = y
  ext n
  simp only [WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt O p => f (y.coeff n))
    (RingHom.ext_zmod ((G : PreTilt O p →+* PreTilt O p).comp (ZMod.castHom (dvd_refl p) _)) _)

theorem frob_symm_comm (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    G ((_root_.frobeniusEquiv (PreTilt O p) p).symm x) =
      (_root_.frobeniusEquiv (PreTilt O p) p).symm (G x) := by
  apply (_root_.frobeniusEquiv (PreTilt O p) p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem wittEquiv_phiInv (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    wittEquiv G (phiInv p O a) = phiInv p O (wittEquiv G a) := by
  ext n
  simp [wittEquiv_apply, phiInv, WittVector.map_coeff, frob_symm_comm]

theorem wittEquiv_teich (G : PreTilt O p ≃+* PreTilt O p) (x : PreTilt O p) :
    wittEquiv G (WittVector.teichmuller p x) = WittVector.teichmuller p (G x) := by
  rw [wittEquiv_apply, WittVector.map_teichmuller]; rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def wittAlgEquiv (G : PreTilt O p ≃+* PreTilt O p) : Ainf p O ≃ₐ[ℤ_[p]] Ainf p O :=
  AlgEquiv.ofRingEquiv (f := wittEquiv G) (fun x => wittEquiv_ofPadic G x)

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

def tensorEquiv (G : PreTilt O p ≃+* PreTilt O p) : RL p O Λ ≃+* RL p O Λ :=
  (Algebra.TensorProduct.congr (wittAlgEquiv G) (AlgEquiv.refl : Λ ≃ₐ[ℤ_[p]] Λ)).toRingEquiv

theorem tensorEquiv_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    tensorEquiv Λ G (a ⊗ₜ l) = wittEquiv G a ⊗ₜ l := rfl

theorem tensorEquiv_symm_tmul (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) (l : Λ) :
    (tensorEquiv Λ G).symm (a ⊗ₜ l) = (wittEquiv G).symm a ⊗ₜ l := rfl

end GlobalTheory.GammaAct

namespace GlobalTheory.GammaAct

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem map_root (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    G (root ε) = root (G ε) := frob_symm_comm G ε

theorem wittEquiv_xi (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (xi ε) = xi (G ε) := by
  simp only [xi, map_sum, map_pow, wittEquiv_teich, map_root]

theorem wittEquiv_mu (G : PreTilt O p ≃+* PreTilt O p) (ε : PreTilt O p) :
    wittEquiv G (mu ε) = mu (G ε) := by
  simp only [mu, map_sub, map_one, wittEquiv_teich]

theorem tensorEquiv_inA (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
    (G : PreTilt O p ≃+* PreTilt O p) (a : Ainf p O) :
    tensorEquiv Λ G (inA a) = inA (wittEquiv G a) := rfl

end

theorem exists_tensor_action : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (γ : O ≃+* O), IsPsi ψ → IsPrimitiveRoot (root ε).untilt p → ∃ (Γ : RL p O Λ ≃+* RL p O Λ) (ε' : PreTilt O p), IsPrimitiveRoot (root ε').untilt p ∧ Γ (inA (xi ε)) = inA (xi ε') ∧ Γ (inA (mu ε)) = inA (mu ε') ∧ (∀ r, Γ (ψ r) = ψ (Γ r)) ∧ ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → ∃ f', IsTheta ((γ : O →+* O).comp σ) f' ∧ ∀ r, f' (Γ r) = γ (f r) := by
  intro p _ O _ _ _ ε Λ _ _ ψ γ hψ hε
  obtain ⟨G, hu, hθ⟩ := GlobalTheory.T.tilt_lift_of_ring_automorphism p O γ
  refine ⟨tensorEquiv Λ G, G ε, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_root, hu]
    exact hε.map_of_injective γ.injective
  · rw [tensorEquiv_inA, wittEquiv_xi]
  · rw [tensorEquiv_inA, wittEquiv_mu]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, tensorEquiv_tmul, tensorEquiv_tmul, hψ, wittEquiv_phiInv]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro σ f hf
    refine ⟨((γ : O →+* O).comp f).comp ((tensorEquiv Λ G).symm : RL p O Λ →+* RL p O Λ),
      fun a l => ?_, fun r => by simp⟩
    have h := hθ ((wittEquiv G).symm a)
    rw [← wittEquiv_apply, RingEquiv.apply_symm_apply] at h
    show γ (f ((tensorEquiv Λ G).symm (a ⊗ₜ l))) = _ * γ (σ l)
    rw [tensorEquiv_symm_tmul, hf, map_mul, h]

end GlobalTheory.GammaAct
