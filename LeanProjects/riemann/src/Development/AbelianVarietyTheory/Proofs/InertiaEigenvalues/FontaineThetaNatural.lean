import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.Per

theorem untilt_natural {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : O →+* O) (τ : PreTilt O p →+* PreTilt O p)
    (h : ∀ (x : PreTilt O p) (n : ℕ) (y : O),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y →
        PreTilt.coeff n (τ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (σ y))
    (x : PreTilt O p) : (τ x).untilt = σ x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(p : O)}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) (PreTilt.coeff n x)
  refine ⟨σ y, (h x n y hy.symm).symm, ?_⟩
  have h1 := (Perfection.teichmuller_sModEq (I := Ideal.span {(p : O)}) (x := x) hy).symm
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1 ⊢
  have h2 := map_dvd σ h1
  rw [map_pow, map_natCast, map_sub, map_pow] at h2
  exact h2

theorem fontaineTheta_natural {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : O →+* O) (τ : PreTilt O p →+* PreTilt O p)
    (h : ∀ (x : PreTilt O p) (n : ℕ) (y : O),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y →
        PreTilt.coeff n (τ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (σ y))
    (a : WittVector p (PreTilt O p)) :
    WittVector.fontaineTheta O p (WittVector.map τ a) = σ (WittVector.fontaineTheta O p a) := by
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})).2 fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, ← Ideal.Quotient.eq]
  have key := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)).comp
      ((WittVector.fontaineTheta O p).comp (WittVector.map τ)))
    ((Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)).comp (σ.comp (WittVector.fontaineTheta O p)))
    ⟨n, by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
    (fun x => by
      simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_natural σ τ h])
  exact RingHom.congr_fun key a

end GlobalTheory.Per
