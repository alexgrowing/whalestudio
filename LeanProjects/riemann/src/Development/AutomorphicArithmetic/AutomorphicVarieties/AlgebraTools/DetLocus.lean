import Mathlib

open IsLocalRing MvPolynomial

namespace UpperTheory.V.AlgebraTools

variable {P : Type} [CommRing P] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_map_C (p : Ideal P) [p.IsPrime] :
    (p.map (C : P →+* MvPolynomial ι P)).IsPrime := by
  have he : p.map (C : P →+* MvPolynomial ι P) =
      RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [he]
  exact RingHom.ker_isPrime _

def relIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := Ideal.span (Set.range (z.mulVec m))

def detIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := relIdeal z m ⊔ Ideal.span {z.det}

noncomputable def lam (P : Type) [CommRing P] (c : ι) (j : ι) : MvPolynomial ι P :=
  if j = c then 1 else X j

noncomputable def chartGen (z : Matrix ι ι P) (m : ι → P) (c : ι) :
    ι ⊕ {j : ι // j ≠ c} → MvPolynomial ι P :=
  Sum.elim ((z.map C).mulVec (lam P c)) (fun j => C (m j.1) - lam P c j.1 * C (m c))

noncomputable def chartIdeal (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal (MvPolynomial ι P) :=
  Ideal.span (Set.range (chartGen z m c))

noncomputable def genKer [IsLocalRing P] (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal P where
  carrier := {f | ∃ s : MvPolynomial ι P, s ∉ (maximalIdeal P).map (C : P →+* MvPolynomial ι P) ∧
    s * C f ∈ chartIdeal z m c}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top (by
    have : (maximalIdeal P).IsPrime := inferInstance
    exact isPrime_map_C _)), by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    have hp : ((maximalIdeal P).map (C : P →+* MvPolynomial ι P)).IsPrime :=
      isPrime_map_C _
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * C (a + b) = t * (s * C a) + s * (t * C b) := by rw [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  smul_mem' := by
    rintro r a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have : s * C (r • a) = C r * (s * C a) := by rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha

end UpperTheory.V.AlgebraTools
