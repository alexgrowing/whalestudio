import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open IsLocalRing Polynomial

open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (h : IsZTorsor B D q act) :
    Algebra.Etale B D := by
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  have hmul : ∀ x : D ⊗[B] D, Algebra.TensorProduct.lmul' B x = Φ x 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have hidem : IsIdempotentElem (KaehlerDifferential.ideal B D) := by
    obtain ⟨e, he⟩ := hbij.2 (1 - Pi.single (1 : Multiplicative (ZMod q)) (1 : D))
    have heI : e ∈ KaehlerDifferential.ideal B D := by
      rw [KaehlerDifferential.ideal, RingHom.mem_ker]
      change Algebra.TensorProduct.lmul' B e = 0
      rw [hmul, he]; simp
    apply le_antisymm Ideal.mul_le_left
    intro x hx
    have hx0 : Φ x 1 = 0 := by
      rw [← hmul]
      exact (RingHom.mem_ker).1 hx
    have hxe : x = x * e := by
      apply hbij.1
      rw [map_mul, he]
      funext g
      by_cases hg : g = 1
      · subst hg; simp [hx0]
      · simp [Pi.single_apply, hg]
    rw [hxe]
    exact Ideal.mul_mem_mul hx heI
  haveI : Subsingleton Ω[D⁄B] := (Ideal.cotangent_subsingleton_iff _).2 hidem
  haveI : Algebra.FormallyUnramified B D := ⟨inferInstance⟩
  haveI : Module.Flat B D := inferInstance
  haveI : Module.FinitePresentation B D := Module.finitePresentation_of_projective B D
  haveI : Algebra.FinitePresentation B D :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite B D).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.KeyOriginCut
