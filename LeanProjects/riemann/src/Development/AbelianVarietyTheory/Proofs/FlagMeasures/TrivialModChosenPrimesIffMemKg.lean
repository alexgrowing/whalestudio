import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemExtIdSmulIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Inhab GlobalTheory.Mem.RowsBundle

theorem hAf_add_left (I : AutInst) (x x' y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (x + x') y = hAf I x y + hAf I x' y := by
  unfold hAf Formalism.UG.hform
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hAf_smul_left (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (a • x) y = Formalism.UG.sigR I.cm.sig (Af I.F) a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem mapsTo_conj_of_adjoint (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E))
    (T T' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hc : IsConj I w w')
    (hadj : ∀ x y, hAf I (T' *ᵥ x) y = hAf I x (T *ᵥ y))
    (hT' : ∀ y ∈ I.Lf, T' *ᵥ y ∈ extId I w.asIdeal • I.Lf) :
    ∀ y ∈ I.Lf, T *ᵥ y ∈ extId I w'.asIdeal • I.Lf := by
  intro y hy
  rw [DualIdeal.mem_extId_smul_iff I _ w'.ne_bot]
  intro y' hy'
  rw [← hadj]
  have key : ∀ u ∈ extId I w.asIdeal • I.Lf, ∃ z ∈ extId I w'.asIdeal,
      (z : I.E ⊗[I.F] Af I.F) = hAf I u y := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) (fun u u' hu hu' => ?_)
    · obtain ⟨a', ha', e⟩ := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2 w w' hc a ha
      refine ⟨a' * ⟨_, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy l hl⟩, Ideal.mul_mem_right _ _ ha', ?_⟩
      rw [Subring.coe_mul, e]
      show _ = hAf I ((a : I.E ⊗[I.F] Af I.F) • l) y
      rw [hAf_smul_left]
    · obtain ⟨z, hz, e⟩ := hu
      obtain ⟨z', hz', e'⟩ := hu'
      exact ⟨z + z', add_mem hz hz', by rw [Subring.coe_add, e, e', hAf_add_left]⟩
  exact key _ (hT' y' hy')

theorem PlFrame.trivial_iff {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : x ∈ I.Kset) :
    (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y) ↔
      ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf := by
  have key : ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y ↔
      (I.fmat x - 1) *ᵥ (y : Fin I.n → _) ∈ extId I w.asIdeal • I.Lf := by
    intro y h
    rw [← sub_eq_zero, ← map_sub, fr.c_ker, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  exact ⟨fun H y hy => (key ⟨y, hy⟩ (mulVec_mem hx hy)).1 (H _ _), fun H y h => (key y h).2 (H y.1 y.2)⟩

theorem IsChoice.isRadical_mul {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (hC : IsChoice I g Pl w) :
    (Ideal.span {((g 0 * g 1 : ℕ) : 𝓞 I.E)}).IsRadical := by
  have hc : Nat.Coprime (g 0) (g 1) := (Nat.coprime_primes (hC.1 0) (hC.1 1)).2 hC.2.1
  have hc' : IsCoprime ((g 0 : ℕ) : 𝓞 I.E) ((g 1 : ℕ) : 𝓞 I.E) := Nat.Coprime.cast hc
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.mul_eq_inf_of_isCoprime ((Ideal.isCoprime_span_singleton_iff _ _).2 hc')]
  exact (hC.2.2.1 0).inf (hC.2.2.1 1)

theorem trivial_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N →
    IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
      (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  intro I N g Pl w fr _ hC x hx
  have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
  have hone : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hmem : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ I.Lf := fun y hy => by
    simpa using sub_one_pow_mem hx 1 hy
  have crt := fun y hy => GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I (g 0 * g 1) hone hC.isRadical_mul _ (hmem y hy)
  constructor
  · intro H
    have H1 := fun k v => ((fr k v).trivial_iff hx).1 (H k v)
    have H2 : ∀ k v, ∀ y ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ y ∈ extId I (w k v).asIdeal • I.Lf := by
      intro k v y hy
      have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
      have h := neg_mem (H1 k v _ (mulVec_mem hx' hy))
      rw [Matrix.mulVec_mulVec, sub_mul, h1, one_mul, ← Matrix.neg_mulVec, neg_sub] at h
      exact h
    refine ⟨hx, fun y hy => (crt y hy).1 fun u hu => ?_⟩
    have hk : ∃ k, ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rw [Nat.cast_mul] at hu
      exact (u.isPrime.mem_or_mem hu).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨v, rfl | hv⟩ := hC.2.2.2.2.2.2 k u hk
    · exact H1 k v y hy
    · refine mapsTo_conj_of_adjoint I _ _ _ _ hv (fun a b => ?_) (H2 k v) y hy
      simpa only [pow_one] using hAf_pow_adjoint x 1 a b
  · intro H k v
    refine ((fr k v).trivial_iff hx).2 fun y hy => (crt y hy).2 (H.2 y hy) _ ?_
    have h := (hC.2.2.2.1 k v).1
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.RowLev
