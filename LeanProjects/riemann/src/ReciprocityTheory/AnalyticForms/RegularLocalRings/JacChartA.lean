import Mathlib
import Lemmata.GeneralBFactLeftMore.Imports

namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt

open MvPolynomial IsLocalRing

noncomputable section

variable {n : ℕ}

def ptI (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.eval p : MvPolynomial (Fin n) ℂ →+* ℂ)

instance ptI_isPrime (p : Fin n → ℂ) : (ptI p).IsPrime :=
  RingHom.ker_isPrime _

abbrev localization₂ (p : Fin n → ℂ) : Type :=
  Localization.AtPrime (ptI p)

abbrev locR (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Type :=
  localization₂ p ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K

def gradP (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) : Fin n → ℂ :=
  fun j => eval p (pderiv j h)

def jacS (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (gradP p '' (K : Set (MvPolynomial (Fin n) ℂ)))

theorem mem_ptIdeal {p : Fin n → ℂ} {a : MvPolynomial (Fin n) ℂ} : a ∈ ptI p ↔ eval p a = 0 :=
  RingHom.mem_ker

theorem grad_add (p : Fin n → ℂ) (x y : MvPolynomial (Fin n) ℂ) :
    gradP p (x + y) = gradP p x + gradP p y := by
  ext j; simp [gradP]

theorem grad_mul (p : Fin n → ℂ) (x y : MvPolynomial (Fin n) ℂ) :
    gradP p (x * y) = eval p x • gradP p y + eval p y • gradP p x := by
  ext j; simp [gradP, Derivation.leibniz]

theorem grad_C (p : Fin n → ℂ) (c : ℂ) : gradP p (C c) = 0 := by
  ext j; simp [gradP]

theorem grad_sum (p : Fin n → ℂ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℂ) :
    gradP p (∑ i ∈ s, f i) = ∑ i ∈ s, gradP p (f i) := by
  ext j; simp [gradP, map_sum]

theorem grad_lin (p : Fin n → ℂ) (i : Fin n) : gradP p (X i - C (p i)) = Pi.single i 1 := by
  ext j; simp [gradP, pderiv_X, Pi.single_apply, eq_comm]

theorem sub_C_mem_span_lin (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  first | exact Bl.general_b_fact_left_more.goal1 .. | (apply Bl.general_b_fact_left_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_more.goal1 <;> assumption)

theorem ptIdeal_eq_span (p : Fin n → ℂ) :
    ptI p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro a ha
    have := sub_C_mem_span_lin p a
    rwa [mem_ptIdeal.mp ha, map_zero, sub_zero] at this
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [mem_ptIdeal]

theorem taylor (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) - ∑ i, C (gradP p a i) * (X i - C (p i)) ∈ ptI p ^ 2 := by
  obtain ⟨b, hb⟩ := (Ideal.mem_span_range_iff_exists_fun).mp (sub_C_mem_span_lin p a)
  have ha : a = C (eval p a) + ∑ i, b i * (X i - C (p i)) := by rw [hb]; ring
  have hg : ∀ j, gradP p a j = eval p (b j) := by
    intro j
    have h1 := congrArg (fun f => gradP p f j) ha
    simp only [grad_add, grad_C, grad_sum, grad_mul, grad_lin] at h1
    simpa [Pi.single_apply] using h1
  have : a - C (eval p a) - ∑ i, C (gradP p a i) * (X i - C (p i)) =
      ∑ i, (b i - C (eval p (b i))) * (X i - C (p i)) := by
    rw [← hb]; simp only [hg, sub_mul, Finset.sum_sub_distrib]
  rw [this, pow_two]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul ?_ ?_
  · simp [mem_ptIdeal]
  · simp [mem_ptIdeal]

theorem grad_eq_zero_of_mem_sq (p : Fin n → ℂ) {q : MvPolynomial (Fin n) ℂ}
    (hq : q ∈ ptI p ^ 2) : gradP p q = 0 := by
  rw [pow_two] at hq
  refine Submodule.mul_induction_on hq ?_ ?_
  · intro x hx y hy
    rw [grad_mul, mem_ptIdeal.mp hx, mem_ptIdeal.mp hy]; simp
  · intro x y hx hy; rw [grad_add, hx, hy, add_zero]

def evLoc (p : Fin n → ℂ) : localization₂ p →+* ℂ :=
  IsLocalization.lift (M := (ptI p).primeCompl) (S := localization₂ p)
    (g := (eval p : MvPolynomial (Fin n) ℂ →+* ℂ))
    (fun y => isUnit_iff_ne_zero.mpr fun h => y.2 (mem_ptIdeal.mpr h))

theorem evLoc_algebraMap (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    evLoc p (algebraMap _ (localization₂ p) a) = eval p a :=
  IsLocalization.lift_eq _ _

theorem exists_mul_mem_of_algebraMap_mem (p : Fin n → ℂ) {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {a : MvPolynomial (Fin n) ℂ}
    (h : algebraMap _ (localization₂ p) a ∈ I.map (algebraMap _ (localization₂ p))) :
    ∃ s, s ∉ ptI p ∧ s * a ∈ I := by
  obtain ⟨⟨x, s⟩, hx⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (ptI p).primeCompl (localization₂ p)).mp h
  rw [← map_mul] at hx
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (ptI p).primeCompl (localization₂ p)).mp hx
  refine ⟨c * s, (ptI p).primeCompl.mul_mem c.2 s.2, ?_⟩
  have : (c : MvPolynomial (Fin n) ℂ) * s * a = c * x := by rw [← hc]; ring
  rw [this]; exact I.mul_mem_left _ x.2

variable {p : Fin n → ℂ} (K : Ideal (MvPolynomial (Fin n) ℂ))

abbrev psi (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) : MvPolynomial (Fin n) ℂ →+* locR K p :=
  (Ideal.Quotient.mk _).comp (algebraMap _ (localization₂ p))

theorem le_ptIdeal_of_nontrivial [Nontrivial (locR K p)] : K ≤ ptI p := by
  intro k hk
  by_contra hkp
  have hu : IsUnit (algebraMap _ (localization₂ p) k) :=
    IsLocalization.map_units (localization₂ p) (⟨k, hkp⟩ : (ptI p).primeCompl)
  have htop := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (algebraMap _ (localization₂ p)) hk) hu
  have : (1 : locR K p) = 0 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, htop]
    exact Submodule.mem_top
  exact one_ne_zero this

theorem isUnit_psi {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ ptI p) : IsUnit (psi p K s) :=
  (IsLocalization.map_units (localization₂ p) (⟨s, hs⟩ : (ptI p).primeCompl)).map (Ideal.Quotient.mk _)

def evRing (hK : K ≤ ptI p) : locR K p →+* ℂ :=
  Ideal.Quotient.lift _ (evLoc p) (by
    intro x hx
    have : Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker (evLoc p) := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, RingHom.mem_ker, evLoc_algebraMap]
      exact mem_ptIdeal.mp (hK hk)
    exact RingHom.mem_ker.mp (this hx))

theorem evRing_psi (hK : K ≤ ptI p) (a : MvPolynomial (Fin n) ℂ) :
    evRing K hK (psi p K a) = eval p a := by
  rw [evRing, psi, RingHom.comp_apply, Ideal.Quotient.lift_mk, evLoc_algebraMap]

theorem ker_evRing [IsLocalRing (locR K p)] (hK : K ≤ ptI p) :
    RingHom.ker (evRing K hK) = maximalIdeal (locR K p) := by
  have : (RingHom.ker (evRing K hK)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨psi p K (C c), by rw [evRing_psi, eval_C]⟩)
  exact IsLocalRing.eq_maximalIdeal this

theorem psi_mem_max_iff [IsLocalRing (locR K p)] (hK : K ≤ ptI p)
    (a : MvPolynomial (Fin n) ℂ) : psi p K a ∈ maximalIdeal (locR K p) ↔ a ∈ ptI p := by
  rw [← ker_evRing K hK, RingHom.mem_ker, evRing_psi, mem_ptIdeal]

theorem exists_of_mem_max [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {m : locR K p}
    (hm : m ∈ maximalIdeal (locR K p)) :
    ∃ a s, a ∈ ptI p ∧ s ∉ ptI p ∧ m * psi p K s = psi p K a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj (ptI p).primeCompl x
  have h : Ideal.Quotient.mk _ x * psi p K s = psi p K a := by
    simp only [psi, RingHom.coe_comp, Function.comp_apply, ← hx, map_mul]
  refine ⟨a, s, ?_, s.2, h⟩
  rw [← psi_mem_max_iff K hK, ← h]
  exact Ideal.mul_mem_right _ _ hm

theorem max_eq_map [IsLocalRing (locR K p)] (hK : K ≤ ptI p) :
    maximalIdeal (locR K p) = (ptI p).map (psi p K) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, s, ha, hs, h⟩ := exists_of_mem_max K hK hm
    have hu := isUnit_psi K hs
    have : m = psi p K a * ↑hu.unit⁻¹ := by
      rw [← h, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (psi_mem_max_iff K hK a).mpr ha

theorem psi_mem_sq [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {a : MvPolynomial (Fin n) ℂ}
    (ha : a ∈ ptI p ^ 2) : psi p K a ∈ maximalIdeal (locR K p) ^ 2 := by
  rw [max_eq_map K hK, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

theorem exists_of_psi_mem_sq [IsLocalRing (locR K p)] (hK : K ≤ ptI p)
    {l : MvPolynomial (Fin n) ℂ} (hl : psi p K l ∈ maximalIdeal (locR K p) ^ 2) :
    ∃ s, s ∉ ptI p ∧ s * l ∈ ptI p ^ 2 ⊔ K := by
  rw [max_eq_map K hK, ← Ideal.map_pow, psi, ← Ideal.map_map] at hl
  change Ideal.Quotient.mk _ (algebraMap _ (localization₂ p) l) ∈ _ at hl
  rw [Ideal.mem_quotient_iff_mem_sup, ← Ideal.map_sup] at hl
  exact exists_mul_mem_of_algebraMap_mem p hl

end

end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
