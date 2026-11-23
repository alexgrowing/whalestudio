import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

section NabLin

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f g : PS R n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (t : R) (f : PS R n d) :
    DofN F b u (t • f) = t • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, map_smul, mul_smul_comm, Finset.smul_sum]

theorem dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_add]

theorem dofN_iterate_smul (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (t : R) (f : PS R n d) :
    (DofN F b u)^[k] (t • f) = t • (DofN F b u)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, dofN_smul]

variable {ι : Type} [Fintype ι]

theorem dmonN_add (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f g : PS R n d) :
    DmonN F cp u m (f + g) = DmonN F cp u m f + DmonN F cp u m g := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_add]

theorem dmonN_smul (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (t : R) (f : PS R n d) :
    DmonN F cp u m (t • f) = t • DmonN F cp u m f := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, dofN_iterate_smul]

theorem dpolyN_eq_sum_of_subset (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    DpolyN F cp u P f = ∑ m ∈ s, MvPowerSeries.C (P.coeff m) * DmonN F cp u m f := by
  unfold DpolyN
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, zero_mul]

theorem dpolyN_add_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f g : PS R n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, dmonN_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by
  simp only [DpolyN, dmonN_smul, mul_smul_comm, Finset.smul_sum]

theorem dpolyN_add_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P Q : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (P + Q) f = DpolyN F cp u P f + DpolyN F cp u Q f := by
  classical
  rw [dpolyN_eq_sum_of_subset F cp u (P + Q) f (P.support ∪ Q.support) MvPolynomial.support_add,
    dpolyN_eq_sum_of_subset F cp u P f (P.support ∪ Q.support) Finset.subset_union_left,
    dpolyN_eq_sum_of_subset F cp u Q f (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by
  have hs : (MvPolynomial.C t * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [dpolyN_eq_sum_of_subset F cp u _ f P.support hs, DpolyN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, mul_assoc]

end NabLin

theorem nabValN_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u
  refine ⟨fun f g P => ?_, fun t f P => ?_, fun f P Q => ?_, fun t f P => ?_⟩
  · simp only [nabValN, add_mul, dpolyN_add_right, map_add]
  · simp only [nabValN]
    rw [smul_mul_assoc, dpolyN_smul_right, MvPowerSeries.smul_eq_C_mul, map_mul,
      MvPowerSeries.constantCoeff_C]
  · simp only [nabValN, dpolyN_add_left, map_add]
  · simp only [nabValN]
    rw [dpolyN_C_mul_left, map_mul, MvPowerSeries.constantCoeff_C]

end GlobalTheory
