import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTLower
import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLd

noncomputable section

namespace Formalism.L2.DIV.BrJ

open Formalism.BasicNotions Formalism.MainNotions

theorem branching_interlacing_pairs : PrimeDegreeVariant.Conclusion6 := by
  intro n N h lam sg hI
  exact _root_.gTLower_of Formalism.BasicNotions.factDelDualNabla n N h lam sg hI

variable {D : D7} {u : D.what₂.Word}

private theorem map_intCast_mem_delSq {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ delSq ℤ N lam) : MvPolynomial.map (Int.castRingHom ℂ) f ∈ delSq ℂ N lam := by
  unfold delSq Formalism.GradedWeylDivisibility.weyl at *
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨w, by rw [Formalism.UG.P.wlocal_map_applyWord, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

private theorem isBr_of_eqOn_delSq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br br' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hb : PrimeDegreeVariant.IsBr h lam sg br) (he : Set.EqOn br' br (delSq ℂ N lam : Set _)) :
    PrimeDegreeVariant.IsBr h lam sg br' := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  refine ⟨fun f hf => ?_, fun f hf => ?_, ?_, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [he (map_intCast_mem_delSq lam f hf)]
    exact b1 f hf
  · rw [he hf]
    exact b2 f hf
  · obtain ⟨f, hf, hne⟩ := b3
    exact ⟨f, hf, by rw [he hf]; exact hne⟩
  · rw [he (PI.GTS.sqAct_mem_delSq N lam _ f hf), he hf]
    exact b4 g f hf
  · rw [he (PI.GTS.sqAct_mem_delSq N lam _ f hf), he hf]
    exact b5 a f hf
  · rw [he hf]
    exact b6 f hf

private theorem interlace_lamTr_sgTr (P : product_first_zeroth_parts.Pend D u) (τ : D.what₂.Tau) :
    PrimeDegreeVariant.Interlace (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) := by
  unfold PrimeDegreeVariant.Interlace product_first_zeroth_parts.lamTr product_first_zeroth_parts.sgTr
  simp only [product_first_zeroth_parts.wSh, sub_le_sub_iff_right]
  exact fun i => P.interlace τ i

private theorem isBr_and_isTranspose_lamTr_sgTr (h : ∀ τ : D.what₂.Tau, PrimeDegreeVariant.Interlace (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ))
    (τ : D.what₂.Tau) : ∃ io br, PrimeDegreeVariant.IsIota (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io ∧
      PrimeDegreeVariant.IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) br ∧
      PrimeDegreeVariant.IsTranspose (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io br := by
  have hB := branching_interlacing_pairs _ _ (product_first_zeroth_parts.Nm_succ D.R) _ _ (h τ)
  unfold PrimeDegreeVariant.Branch at hB
  exact hB.2.2.2.2

theorem archimedean_signature_matching_of_brTie (P : product_first_zeroth_parts.Pend D u) (tie : J.BrTie P) : product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro τ
  obtain ⟨io0, br0, hio, hbr, htr⟩ := isBr_and_isTranspose_lamTr_sgTr (interlace_lamTr_sgTr P) τ
  exact isBr_of_eqOn_delSq _ _ _ _ _ hbr (tie τ io0 br0 hio hbr htr)

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.DIV.BrJ
