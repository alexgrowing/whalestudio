import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc

variable {E : Type} [Field E] {n : ℕ}

theorem nrm_succ (σ : E ≃+* E) (q : ℕ) (δ : GL (Fin n) E) :
    nrm σ (q + 1) δ = nrm σ q δ * (sg σ)^[q] δ := by
  simp [nrm, List.range_succ]

theorem sg_iterate_apply (σ : E ≃+* E) (q : ℕ) (x : GL (Fin n) E) (i j : Fin n) :
    (((sg σ)^[q] x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = σ^[q] ((x : Matrix (Fin n) (Fin n) E) i j) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sg_iterate_eq_self {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (x : GL (Fin n) E) : (sg σ)^[q] x = x := by
  apply Units.ext
  ext i j
  rw [sg_iterate_apply, h]

theorem nrm_conj_iterate (σ : E ≃+* E) (q : ℕ) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * (sg σ)^[q] x := by
  induction q with
  | zero => simp [nrm]
  | succ q ih =>
    rw [nrm_succ, nrm_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply]
    group

theorem nrm_conj {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * x := by
  rw [nrm_conj_iterate, sg_iterate_eq_self h]

end UpperTheory.ConvolutionTheory.Loc
