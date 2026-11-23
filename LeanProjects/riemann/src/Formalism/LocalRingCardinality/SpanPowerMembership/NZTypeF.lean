import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeC

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

attribute [local instance] Classical.propDecidable

section Eval

variable {K : Type} [Field K]

def evS {Γ : Type} [Finite Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : K :=
  letI := Fintype.ofFinite Γ
  ∑ g, x.coeff g * ψ g

theorem evS_eq {Γ : Type} [Fintype Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : evS ψ x = ∑ g, x.coeff g * ψ g := by
  unfold evS
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem evS_zero {Γ : Type} [Finite Γ] (ψ : Γ → K) : evS ψ (0 : MonoidAlgebra K Γ) = 0 := by
  simp [evS]

theorem evS_sub {Γ : Type} [Finite Γ] (ψ : Γ → K) (x y : MonoidAlgebra K Γ) : evS ψ (x - y) = evS ψ x - evS ψ y := by
  simp [evS, sub_mul, Finset.sum_sub_distrib]

theorem evS_sum {Γ ι : Type} [Finite Γ] (ψ : Γ → K) (s : Finset ι) (x : ι → MonoidAlgebra K Γ) :
    evS ψ (∑ i ∈ s, x i) = ∑ i ∈ s, evS ψ (x i) := by
  unfold evS
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem evS_one {Γ : Type} [Group Γ] [Finite Γ] (ψ : Γ → K) : evS ψ (1 : MonoidAlgebra K Γ) = ψ 1 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq, Finset.sum_eq_single 1]
  · simp
  · intro g _ hg
    rw [one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem evS_tens (ψ : ∀ i, G i → K) (x : ∀ i, MonoidAlgebra K (G i)) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (tens x) = ∏ i, evS (ψ i) (x i) := by
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  rw [evS_eq]
  simp only [evS_eq, tens_coeff, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i)) (S : (∀ i, L i) → Prop)

theorem evS_eSum (ψ : ∀ i, G i → K) (b : ∀ i, L i) (hb : S b)
    (hδ : ∀ i l, evS (ψ i) (E i l) = if l = b i then 1 else 0) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (eSum E S) = 1 := by
  unfold eSum
  rw [evS_sum, Finset.sum_eq_single b]
  · rw [if_pos hb, evS_tens]
    exact Finset.prod_eq_one fun i _ => by rw [hδ, if_pos rfl]
  · intro a _ hab
    split_ifs
    · rw [evS_tens]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hδ, if_neg hi])
    · exact evS_zero _
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lift_scalar {Γ V : Type} [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (Ψ : Γ →* K)
    (F : Γ →* Module.End K V) (hF : ∀ g, F g = Ψ g • 1) (x : MonoidAlgebra K Γ) :
    MonoidAlgebra.lift K (Module.End K V) Γ F x = evS Ψ x • 1 := by
  have := Fintype.ofFinite Γ
  rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ (fun a b => b • F a) (fun _ => zero_smul _ _), evS_eq,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun g _ => by rw [hF, smul_smul]

end Eval

section Triv

variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]

def eT : MonoidAlgebra K Γ := MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun _ => ((Nat.card Γ : K))⁻¹

variable {K Γ}

theorem eT_coeff (g : Γ) : (eT K Γ).coeff g = ((Nat.card Γ : K))⁻¹ := rfl

theorem card_ne [CharZero K] : (Nat.card Γ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

theorem eT_idem [CharZero K] : eT K Γ * eT K Γ = eT K Γ := by
  have := Fintype.ofFinite Γ
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype]
  simp only [eT_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [← mul_assoc, mul_inv_cancel₀ card_ne, one_mul]

theorem eT_central (a : MonoidAlgebra K Γ) : eT K Γ * a = a * eT K Γ :=
  commute_of_single _ (fun g => by
    apply MonoidAlgebra.coeff_injective
    ext h
    rw [coeff_mul_single_apply, coeff_single_mul_apply, eT_coeff, eT_coeff, mul_one, one_mul]) a

theorem eT_ne_zero [CharZero K] : eT K Γ ≠ 0 := fun h =>
  inv_ne_zero (card_ne (K := K) (Γ := Γ)) (congrArg (fun x => x.coeff 1) h)

theorem one_sub_eT_ne_zero [CharZero K] (g : Γ) (hg : g ≠ 1) : 1 - eT K Γ ≠ 0 := fun h => by
  have h1 := congrArg (fun x => x.coeff g) h
  simp only [coeff_sub, Finsupp.sub_apply, eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg),
    zero_sub] at h1
  exact inv_ne_zero (card_ne (K := K) (Γ := Γ)) (neg_eq_zero.mp h1)

theorem evS_eT_one [CharZero K] : evS (fun _ : Γ => (1 : K)) (eT K Γ) = 1 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq]
  simp only [eT_coeff, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  exact mul_inv_cancel₀ card_ne

theorem evS_eT_ne (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) : evS ψ (eT K Γ) = 0 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq]
  simp only [eT_coeff, ← Finset.mul_sum]
  have h1 : ψ g * ∑ x, ψ x = ∑ x, ψ x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g) (fun x => ψ x)]
    exact Finset.sum_congr rfl fun x _ => (map_mul ψ g x).symm
  have h2 : (ψ g - 1) * ∑ x, ψ x = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rw [(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hg), mul_zero]

end Triv

section Family

variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)

def esZ (f : Λ) : MonoidAlgebra K Γ := if f = fA then 1 - eT K Γ else if f = fB then eT K Γ else 0

def cfQ (f : Λ) (h : Γ) : ℚ :=
  if f = fA then (if (1 : Γ) = h then 1 else 0) - ((Nat.card Γ : ℚ))⁻¹
  else if f = fB then ((Nat.card Γ : ℚ))⁻¹ else 0

theorem esZ_coeff [CharZero K] (f : Λ) (h : Γ) : (esZ K Γ fA fB f).coeff h = (cfQ Γ fA fB f h : K) := by
  unfold esZ cfQ
  split_ifs <;> simp [eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, *]

variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)

theorem esZ_idem (f : Λ) : esZ K Γ fA fB f * esZ K Γ fA fB f = esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, mul_sub, eT_idem, one_mul, one_mul, mul_one, sub_self, sub_zero]
  · exact eT_idem
  · simp

omit [CharZero K] in
theorem esZ_central (f : Λ) (a) : esZ K Γ fA fB f * a = a * esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, eT_central, one_mul, mul_one]
  · exact eT_central a
  · simp

theorem esZ_orth (f f' : Λ) (h : f ≠ f') : esZ K Γ fA fB f * esZ K Γ fA fB f' = 0 := by
  unfold esZ
  split_ifs with h1 h2' h3 h4 h5 h6
  · exact absurd (h1.trans h2'.symm) h
  · rw [sub_mul, eT_idem, one_mul, sub_self]
  · simp
  · rw [mul_sub, eT_idem, mul_one, sub_self]
  · exact absurd (h4.trans h6.symm) h
  all_goals simp

omit [CharZero K] in
include hAB in
theorem esZ_sum (S : Finset Λ) (hA : fA ∈ S) (hB : fB ∈ S) : ∑ f ∈ S, esZ K Γ fA fB f = 1 := by
  have e : ∀ f, esZ K Γ fA fB f = (if f = fA then 1 - eT K Γ else 0) + if f = fB then eT K Γ else 0 := fun f => by
    unfold esZ
    by_cases h1 : f = fA
    · rw [if_pos h1, if_pos h1, if_neg (fun h => hAB (h1.symm.trans h)), add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hA, if_pos hB, sub_add_cancel]

include hAB in

theorem evS_esZ_one (f : Λ) : evS (fun _ : Γ => (1 : K)) (esZ K Γ fA fB f) = if f = fB then 1 else 0 := by
  unfold esZ
  by_cases h1 : f = fA
  · rw [if_pos h1, if_neg (fun h => hAB (h1.symm.trans h)), evS_sub, evS_one, evS_eT_one, sub_self]
  · rw [if_neg h1]
    split_ifs
    · exact evS_eT_one
    · exact evS_zero _

include hAB in

theorem evS_esZ_ne (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) (f : Λ) :
    evS ψ (esZ K Γ fA fB f) = if f = fA then 1 else 0 := by
  unfold esZ
  by_cases h1 : f = fA
  · rw [if_pos h1, if_pos h1, evS_sub, evS_one, evS_eT_ne ψ g hg, map_one, sub_zero]
  · rw [if_neg h1, if_neg h1]
    split_ifs
    · exact evS_eT_ne ψ g hg
    · exact evS_zero _

end Family

end Formalism.BasicNotions.Examples₂.NZ
