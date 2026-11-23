import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QuadraticGaussSumPowEightEqCardMulRadicalPowFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GaussPow

theorem reps_bij {V : Type} [AddCommGroup V] {A B : AddSubgroup V} {T : Finset V} (h : IsReps A B T) :
    Function.Bijective (fun y : T => (QuotientAddGroup.mk ⟨y.1, h.1 y.1 y.2⟩ : B ⧸ A.addSubgroupOf B)) := by
  obtain ⟨hT, hu⟩ := h
  constructor
  · rintro ⟨y1, hy1⟩ ⟨y2, hy2⟩ hxy
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg] at hxy
    obtain ⟨z, _, hz⟩ := hu y1 (hT y1 hy1)
    have a1 := hz y1 ⟨hy1, by simp⟩
    have a2 : y2 = z := by
      refine hz y2 ⟨hy2, ?_⟩
      have e : y1 - y2 = -(-y1 + y2) := by abel
      rw [e]
      exact A.neg_mem hxy
    exact Subtype.ext (a1.trans a2.symm)
  · intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, ⟨hyT, hxy⟩, _⟩ := hu x.1 x.2
    refine ⟨⟨y, hyT⟩, ?_⟩
    simp only [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    have e : -y + x.1 = x.1 - y := by abel
    rw [e]
    exact hxy

theorem reps_card {V : Type} [AddCommGroup V] {A B : AddSubgroup V} {T : Finset V} (h : IsReps A B T) :
    T.card = A.relIndex B := by
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_eq_of_bijective _ (reps_bij h)]
  simp

theorem card_image {V : Type} [AddCommGroup V] {A B C : AddSubgroup V} (hCB : C ≤ B)
    (P : B ⧸ A.addSubgroupOf B → Prop) (hAC : A ≤ C)
    (hP : ∀ x : B, P (QuotientAddGroup.mk x) ↔ x.1 ∈ C) :
    Nat.card {u // P u} = A.relIndex C := by
  let g : C →+ B ⧸ A.addSubgroupOf B :=
    (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion hCB)
  have hker : g.ker = A.addSubgroupOf C := by
    ext x
    simp [g, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  have hrange : ∀ u, u ∈ g.range ↔ P u := by
    intro u
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [hP]
    constructor
    · rintro ⟨c, hc⟩
      simp only [g, AddMonoidHom.coe_comp, Function.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg] at hc
      have e : x.1 = (c : V) + (-(AddSubgroup.inclusion hCB c : V) + x.1) := by
        simp
      rw [e]
      exact C.add_mem c.2 (hAC hc)
    · intro hx
      exact ⟨⟨x.1, hx⟩, rfl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
  exact (Nat.card_congr (Equiv.subtypeEquivRight hrange)).symm

theorem gauss_reps {V : Type} [AddCommGroup V] {A B C : AddSubgroup V} {T : Finset V} (h : IsReps A B T)
    (hAC : A ≤ C) (hCB : C ≤ B) (f : V → ℂ) (g : V → V → ℂ) (e : ℕ) (he : 0 < e)
    (h1 : ∀ x ∈ B, f x ^ e = 1) (h2 : ∀ x y, f (x + y) = f x * f y * g x y)
    (h3 : ∀ x y z, g (x + y) z = g x z * g y z) (h4 : ∀ (n : ℤ) x, f (n • x) = f x ^ (n ^ 2))
    (h5 : ∀ x ∈ B, ∀ l ∈ A, f (x + l) = f x)
    (h6 : ∀ u ∈ B, (∀ x ∈ B, g u x = 1) ↔ u ∈ C) (h7 : ∀ u ∈ C, f u = 1) :
    (∑ x ∈ T, f x) ^ 8 = ((T.card : ℂ) * (A.relIndex C : ℂ)) ^ 4 := by
  classical
  have hbij := reps_bij h
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Finite.of_surjective _ hbij.2
  letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
  have hf0 : f 0 = 1 := by simpa using h4 0 0
  have hfne : ∀ x ∈ B, f x ≠ 0 := by
    intro x hx h0
    have := h1 x hx
    rw [h0, zero_pow he.ne'] at this
    exact zero_ne_one this
  have hgsymm : ∀ x ∈ B, ∀ y ∈ B, g x y = g y x := by
    intro x hx y hy
    have e1 := h2 x y
    have e2 := h2 y x
    rw [add_comm y x] at e2
    have h' : f x * f y * (g x y - g y x) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (mul_ne_zero (hfne x hx) (hfne y hy))
    · linear_combination h''
  have hfP : ∀ x ∈ B, ∀ y, y - x ∈ A → f y = f x := by
    intro x hx y hl
    have e : y = x + (y - x) := by abel
    rw [e]; exact h5 x hx _ hl
  have hgC : ∀ l ∈ C, ∀ z ∈ B, g l z = 1 := fun l hl z hz => (h6 l (hCB hl)).mpr hl z hz
  have hgP1 : ∀ x ∈ B, ∀ y, y - x ∈ A → ∀ z ∈ B, g y z = g x z := by
    intro x hx y hl z hz
    have e : y = x + (y - x) := by abel
    rw [e, h3, hgC _ (hAC hl) z hz, mul_one]
  have hgadd2 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, g x (y + z) = g x y * g x z := by
    intro x hx y hy z hz
    rw [hgsymm x hx _ (B.add_mem hy hz), h3, hgsymm y hy x hx, hgsymm z hz x hx]
  have hgP2 : ∀ x ∈ B, ∀ y, y - x ∈ A → ∀ z ∈ B, g z y = g z x := by
    intro x hx y hl z hz
    have hy : y ∈ B := by
      have e : y = x + (y - x) := by abel
      rw [e]; exact B.add_mem hx ((hAC.trans hCB) hl)
    rw [hgsymm z hz y hy, hgsymm z hz x hx]
    exact hgP1 x hx y hl z hz
  let r : (B ⧸ A.addSubgroupOf B) → V := fun q => ((Quotient.out q : B) : V)
  have hrB : ∀ q, r q ∈ B := fun q => (Quotient.out q).2
  have hmk : ∀ q : B ⧸ A.addSubgroupOf B, (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = q :=
    fun q => Quotient.out_eq q
  have hrmk : ∀ x : B, r (QuotientAddGroup.mk x) - x.1 ∈ A := by
    intro x
    have e := hmk (QuotientAddGroup.mk x : B ⧸ A.addSubgroupOf B)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e
    have e2 : r (QuotientAddGroup.mk x) - x.1 =
        -((-(Quotient.out (QuotientAddGroup.mk x : B ⧸ A.addSubgroupOf B)) + x : B) : V) := by
      simp only [r, AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
    rw [e2]; exact A.neg_mem e
  have hr_add : ∀ p q, r (p + q) - (r p + r q) ∈ A := by
    intro p q
    have e := hrmk (Quotient.out p + Quotient.out q)
    rw [QuotientAddGroup.mk_add, hmk, hmk] at e
    simp only [AddSubgroup.coe_add] at e
    exact e
  have hr_smul : ∀ (m : ℤ) p, r (m • p) - m • r p ∈ A := by
    intro m p
    have e := hrmk (m • Quotient.out p)
    rw [QuotientAddGroup.mk_zsmul, hmk] at e
    simp only [AddSubgroup.coe_zsmul] at e
    exact e
  let Fq : (B ⧸ A.addSubgroupOf B) → ℂ := fun q => f (r q)
  let Gq : (B ⧸ A.addSubgroupOf B) → (B ⧸ A.addSubgroupOf B) → ℂ := fun p q => g (r p) (r q)
  have hFadd : ∀ p q, Fq (p + q) = Fq p * Fq q * Gq p q := by
    intro p q
    show f (r (p + q)) = f (r p) * f (r q) * g (r p) (r q)
    rw [hfP _ (B.add_mem (hrB p) (hrB q)) _ (hr_add p q), h2]
  have hGadd1 : ∀ p q s, Gq (p + q) s = Gq p s * Gq q s := by
    intro p q s
    show g (r (p + q)) (r s) = g (r p) (r s) * g (r q) (r s)
    rw [hgP1 _ (B.add_mem (hrB p) (hrB q)) _ (hr_add p q) _ (hrB s), h3]
  have hGadd2 : ∀ p q s, Gq s (p + q) = Gq s p * Gq s q := by
    intro p q s
    show g (r s) (r (p + q)) = g (r s) (r p) * g (r s) (r q)
    rw [hgP2 _ (B.add_mem (hrB p) (hrB q)) _ (hr_add p q) _ (hrB s),
      hgadd2 _ (hrB s) _ (hrB p) _ (hrB q)]
  have hFsmul : ∀ (m : ℤ) p, Fq (m • p) = Fq p ^ (m ^ 2) := by
    intro m p
    show f (r (m • p)) = f (r p) ^ (m ^ 2)
    rw [hfP _ (zsmul_mem (hrB p) m) _ (hr_smul m p), h4]
  have hFe : ∀ q, Fq q ^ e = 1 := fun q => h1 _ (hrB q)
  have hFne : ∀ q, Fq q ≠ 0 := fun q => hfne _ (hrB q)
  have hGne : ∀ p q, Gq p q ≠ 0 := by
    intro p q h0
    have := hFadd p q
    rw [h0, mul_zero] at this
    exact hFne _ this
  let φ : (B ⧸ A.addSubgroupOf B) → Additive ℂˣ := fun q => Additive.ofMul (Units.mk0 (Fq q) (hFne q))
  let β : (B ⧸ A.addSubgroupOf B) → (B ⧸ A.addSubgroupOf B) → Additive ℂˣ :=
    fun p q => Additive.ofMul (Units.mk0 (Gq p q) (hGne p q))
  have hext : ∀ u v : Additive ℂˣ, ((Additive.toMul u : ℂˣ) : ℂ) = ((Additive.toMul v : ℂˣ) : ℂ) → u = v :=
    fun u v huv => Additive.toMul.injective (Units.ext huv)
  have hφadd : ∀ p q, φ (p + q) = φ p + φ q + β p q := by
    intro p q; apply hext; simp [φ, β, hFadd]
  have hβadd1 : ∀ p q s, β (p + q) s = β p s + β q s := by
    intro p q s; apply hext; simp [β, hGadd1]
  have hβadd2 : ∀ p q s, β s (p + q) = β s p + β s q := by
    intro p q s; apply hext; simp [β, hGadd2]
  have hφsmul : ∀ (m : ℤ) p, φ (m • p) = (m ^ 2) • φ p := by
    intro m p; apply hext; simp [φ, hFsmul]
  have hφe : ∀ q, (e : ℤ) • φ q = 0 := by
    intro q; apply hext; simp [φ, hFe]
  have hβz1 : ∀ (m : ℤ) p q, β (m • p) q = m • β p q := fun m p q =>
    map_zsmul (AddMonoidHom.mk' (fun p => β p q) (fun p p' => hβadd1 p p' q)) m p
  have hβz2 : ∀ (m : ℤ) p q, β q (m • p) = m • β q p := fun m p q =>
    map_zsmul (AddMonoidHom.mk' (fun p => β q p) (fun p p' => hβadd2 p p' q)) m p
  obtain ⟨za, zb, zc, zd, hs⟩ : ∃ za zb zc zd : ℤ, za ^ 2 + zb ^ 2 + zc ^ 2 + zd ^ 2 =
      (Fintype.card (B ⧸ A.addSubgroupOf B) : ℤ) * (e : ℤ) - 1 := by
    obtain ⟨a0, b0, c0, d0, habcd⟩ :=
      Nat.sum_four_squares (Fintype.card (B ⧸ A.addSubgroupOf B) * e - 1)
    refine ⟨a0, b0, c0, d0, ?_⟩
    have h1le : 1 ≤ Fintype.card (B ⧸ A.addSubgroupOf B) * e := Nat.mul_pos Fintype.card_pos he
    have := congrArg (fun n : ℕ => (n : ℤ)) habcd
    push_cast [Nat.cast_sub h1le] at this
    linarith
  have hsQ : ∀ q : B ⧸ A.addSubgroupOf B, (za ^ 2 + zb ^ 2 + zc ^ 2 + zd ^ 2) • q = -q := by
    intro q
    have h0 : ((Fintype.card (B ⧸ A.addSubgroupOf B) : ℤ)) • q = 0 := by
      rw [natCast_zsmul]; exact card_nsmul_eq_zero
    rw [hs, sub_smul, one_smul, mul_comm, mul_smul, h0, smul_zero, zero_sub]
  have hsφ : ∀ q, (za ^ 2 + zb ^ 2 + zc ^ 2 + zd ^ 2) • φ q = -φ q := by
    intro q
    rw [hs, sub_smul, one_smul, mul_smul, hφe, smul_zero, zero_sub]
  let Φ : (Fin 4 → B ⧸ A.addSubgroupOf B) → (Fin 4 → B ⧸ A.addSubgroupOf B) := fun x =>
    ![za • x 0 + (-zb) • x 1 + (-zc) • x 2 + (-zd) • x 3,
      zb • x 0 + za • x 1 + (-zd) • x 2 + zc • x 3,
      zc • x 0 + zd • x 1 + za • x 2 + (-zb) • x 3,
      zd • x 0 + (-zc) • x 1 + zb • x 2 + za • x 3]
  let Ψ : (Fin 4 → B ⧸ A.addSubgroupOf B) → (Fin 4 → B ⧸ A.addSubgroupOf B) := fun y =>
    ![za • y 0 + zb • y 1 + zc • y 2 + zd • y 3,
      (-zb) • y 0 + za • y 1 + zd • y 2 + (-zc) • y 3,
      (-zc) • y 0 + (-zd) • y 1 + za • y 2 + zb • y 3,
      (-zd) • y 0 + zc • y 1 + (-zb) • y 2 + za • y 3]
  have hΦ0 : ∀ x, Φ x 0 = za • x 0 + (-zb) • x 1 + (-zc) • x 2 + (-zd) • x 3 := fun x => rfl
  have hΦ1 : ∀ x, Φ x 1 = zb • x 0 + za • x 1 + (-zd) • x 2 + zc • x 3 := fun x => rfl
  have hΦ2 : ∀ x, Φ x 2 = zc • x 0 + zd • x 1 + za • x 2 + (-zb) • x 3 := fun x => rfl
  have hΦ3 : ∀ x, Φ x 3 = zd • x 0 + (-zc) • x 1 + zb • x 2 + za • x 3 := fun x => rfl
  have hΨΦ : ∀ x, Ψ (Φ x) = -x := by
    intro x
    funext i
    fin_cases i
    · show za • Φ x 0 + zb • Φ x 1 + zc • Φ x 2 + zd • Φ x 3 = -x 0
      rw [hΦ0, hΦ1, hΦ2, hΦ3]
      linear_combination (norm := module) hsQ (x 0)
    · show (-zb) • Φ x 0 + za • Φ x 1 + zd • Φ x 2 + (-zc) • Φ x 3 = -x 1
      rw [hΦ0, hΦ1, hΦ2, hΦ3]
      linear_combination (norm := module) hsQ (x 1)
    · show (-zc) • Φ x 0 + (-zd) • Φ x 1 + za • Φ x 2 + zb • Φ x 3 = -x 2
      rw [hΦ0, hΦ1, hΦ2, hΦ3]
      linear_combination (norm := module) hsQ (x 2)
    · show (-zd) • Φ x 0 + zc • Φ x 1 + (-zb) • Φ x 2 + za • Φ x 3 = -x 3
      rw [hΦ0, hΦ1, hΦ2, hΦ3]
      linear_combination (norm := module) hsQ (x 3)
  have hΦbij : Function.Bijective Φ := by
    refine Finite.injective_iff_bijective.mp (fun x y hxy => ?_)
    have := congrArg Ψ hxy
    rw [hΨΦ, hΨΦ] at this
    exact neg_inj.mp this
  have hrow : ∀ x : Fin 4 → B ⧸ A.addSubgroupOf B, ∑ i, φ (Φ x i) = ∑ i, -φ (x i) := by
    intro x
    rw [Fin.sum_univ_four, Fin.sum_univ_four, hΦ0, hΦ1, hΦ2, hΦ3]
    simp only [hφadd, hφsmul, hβadd1, hβadd2, hβz1, hβz2]
    linear_combination (norm := module) hsφ (x 0) + hsφ (x 1) + hsφ (x 2) + hsφ (x 3)
  have hpow4 : ∀ H : (B ⧸ A.addSubgroupOf B) → ℂ,
      (∑ q, H q) ^ 4 = ∑ x : Fin 4 → B ⧸ A.addSubgroupOf B, ∏ i, H (x i) := by
    intro H
    rw [← Fintype.prod_sum]
    simp
  have hprod : ∀ y : Fin 4 → B ⧸ A.addSubgroupOf B,
      ∏ i, Fq (y i) = ((Additive.toMul (∑ i, φ (y i)) : ℂˣ) : ℂ) := by
    intro y; simp [φ, toMul_sum, Units.coe_prod]
  have hprodinv : ∀ y : Fin 4 → B ⧸ A.addSubgroupOf B,
      ∏ i, (Fq (y i))⁻¹ = ((Additive.toMul (∑ i, -φ (y i)) : ℂˣ) : ℂ) := by
    intro y; simp [φ, toMul_sum, Units.coe_prod]
  have h44 : (∑ q, Fq q) ^ 4 = (∑ q, (Fq q)⁻¹) ^ 4 := by
    rw [hpow4 Fq, hpow4 (fun q => (Fq q)⁻¹),
      show (∑ x : Fin 4 → B ⧸ A.addSubgroupOf B, ∏ i, Fq (x i)) = ∑ x, ∏ i, Fq (Φ x i) from
        (hΦbij.sum_comp (fun y => ∏ i, Fq (y i))).symm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hprod (Φ x), hprodinv x, hrow x]
  have hchar : ∀ u, ∑ q, Gq u q =
      if r u ∈ C then (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) else 0 := by
    intro u
    split_ifs with hu
    · have h1' : ∀ q, Gq u q = 1 := fun q => (h6 (r u) (hrB u)).mpr hu (r q) (hrB q)
      simp [h1']
    · have hn' : ¬ ∀ x ∈ B, g (r u) x = 1 := fun hh => hu ((h6 _ (hrB u)).mp hh)
      push_neg at hn'
      obtain ⟨x, hxB, hx1⟩ := hn'
      have hq0 : Gq u (QuotientAddGroup.mk (⟨x, hxB⟩ : B)) ≠ 1 := by
        show g (r u) (r (QuotientAddGroup.mk (⟨x, hxB⟩ : B))) ≠ 1
        rw [hgP2 x hxB _ (hrmk ⟨x, hxB⟩) _ (hrB u)]
        exact hx1
      have hsh : ∑ q, Gq u q = (∑ q, Gq u q) * Gq u (QuotientAddGroup.mk (⟨x, hxB⟩ : B)) := by
        have hs1 : ∑ q, Gq u q = ∑ q, Gq u (q + QuotientAddGroup.mk (⟨x, hxB⟩ : B)) :=
          (Fintype.sum_equiv (Equiv.addRight
            (QuotientAddGroup.mk (⟨x, hxB⟩ : B) : B ⧸ A.addSubgroupOf B))
            (fun q => Gq u (q + QuotientAddGroup.mk (⟨x, hxB⟩ : B))) (fun q => Gq u q)
            (fun q => rfl)).symm
        rw [Finset.sum_mul]
        rw [hs1]
        exact Finset.sum_congr rfl (fun q _ => hGadd2 _ _ _)
      have h' : (∑ q, Gq u q) * (Gq u (QuotientAddGroup.mk (⟨x, hxB⟩ : B)) - 1) = 0 := by
        linear_combination -hsh
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd (sub_eq_zero.mp h'') hq0
  have hmul : (∑ q, Fq q) * (∑ q, (Fq q)⁻¹) =
      (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) * (Fintype.card {u // r u ∈ C} : ℂ) := by
    calc (∑ q, Fq q) * (∑ q, (Fq q)⁻¹) = ∑ q, ∑ p, Fq p * (Fq q)⁻¹ := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]
      _ = ∑ q, ∑ u, Fq u * Gq u q := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [← Fintype.sum_equiv (Equiv.addRight q) (fun u => Fq (u + q) * (Fq q)⁻¹)
            (fun p => Fq p * (Fq q)⁻¹) (fun u => rfl)]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [hFadd, mul_right_comm (Fq u) (Fq q), mul_assoc (Fq u * Gq u q),
            mul_inv_cancel₀ (hFne q), mul_one]
      _ = ∑ u, Fq u * ∑ q, Gq u q := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ u, if r u ∈ C then (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) else 0 := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [hchar u]
          split_ifs with hu
          · rw [show Fq u = 1 from h7 _ hu, one_mul]
          · rw [mul_zero]
      _ = _ := by
          simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul, Fintype.card_subtype]
          ring
  have hcardQ : Fintype.card (B ⧸ A.addSubgroupOf B) = T.card := by
    rw [reps_card h, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  have hcardC : Fintype.card {u // r u ∈ C} = A.relIndex C := by
    rw [← Nat.card_eq_fintype_card]
    refine card_image hCB (fun u => r u ∈ C) hAC (fun x => ?_)
    show r (QuotientAddGroup.mk x) ∈ C ↔ x.1 ∈ C
    have hl := hAC (hrmk x)
    constructor
    · intro hx
      have e : x.1 = r (QuotientAddGroup.mk x) - (r (QuotientAddGroup.mk x) - x.1) := by abel
      rw [e]; exact C.sub_mem hx hl
    · intro hx
      have e : r (QuotientAddGroup.mk x) = x.1 + (r (QuotientAddGroup.mk x) - x.1) := by abel
      rw [e]; exact C.add_mem hx hl
  have hS : ∑ x ∈ T, f x = ∑ q, Fq q := by
    rw [← Finset.sum_coe_sort T, ← hbij.sum_comp Fq]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    show f y.1 = f (r (QuotientAddGroup.mk ⟨y.1, h.1 y.1 y.2⟩))
    exact (hfP _ (h.1 y.1 y.2) _ (hrmk ⟨y.1, h.1 y.1 y.2⟩)).symm
  have hfin : (∑ q, Fq q) ^ 8 = ((∑ q, Fq q) * (∑ q, (Fq q)⁻¹)) ^ 4 := by
    rw [mul_pow, ← h44]; ring
  rw [hS, hfin, hmul, hcardQ, hcardC]

theorem et_zsmul {F : Type} [Field F] [NumberField F] (n : ℤ) (x : F) : et ((n : F) * x) = et x ^ n := by
  unfold et
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast,
    ← Complex.exp_int_mul]
  congr 1
  ring

end GlobalTheory.HilbertThetaSeries.GaussPow

namespace GlobalTheory.HilbertThetaSeries

open GaussPow in

theorem gaussSum_pow_eight : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → (wC k t c c * ∑ x ∈ T, et (a / c * QF G x)) ^ 8 = 1 := by
  intro F _ _ κ _ _ G hG t ht k hk N a b c d T hN hdual ha hb hcN hd hadbc hc0 hT
  classical
  obtain ⟨hsym, hlin, hadd, hint, hLL, haL, het, hLd⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  obtain ⟨-, -, -, hdsmul, hidx⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hNI : IsIntegral ℤ (N : F) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := (N : ℤ)))
  have hcI : IsIntegral ℤ c := by
    have e : c = (N : F) * (c / N) := by rw [mul_div_cancel₀ c hN0]
    rw [e]; exact hNI.mul hcN
  have hsmulL : ∀ z : F, IsIntegral ℤ z → ∀ x ∈ LL F κ, z • x ∈ LL F κ := by
    intro z hz x hx
    rw [hLL] at hx ⊢
    intro i
    simpa using hz.mul (hx i)
  have hB : ∀ x, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := by
    intro x
    rw [haL]
    constructor
    · rintro ⟨l, hl, rfl⟩; simpa using hl
    · intro hx; exact ⟨x, hx, by simp⟩
  have hdualmem : ∀ y, y ∈ dualL F G ↔ ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n :=
    fun y => Iff.rfl
  have hetI : ∀ z, IsIntegral ℤ z → et z = 1 := fun z hz => (het z 0).2.2.2 hz
  have het_add : ∀ x y : F, et (x + y) = et x * et y := fun x y => (het x y).1
  have het_one : ∀ z : F, et z = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F z = n := fun z => (het z 0).2.2.1
  have hQ0 : QF G (0 : κ → F) = 0 := by
    have := (hlin 0 0 0).2.1
    simpa using this
  let f : (κ → F) → ℂ := fun x => et (a / c * QF G x)
  let g : (κ → F) → (κ → F) → ℂ := fun x y => et (a / c * BF G x y)
  let C : AddSubgroup (κ → F) := aL κ (1 : F) ⊓
    (dualL F G).comap (DistribMulAction.toAddMonoidHom (κ → F) (a / c))
  have hCmem : ∀ u, u ∈ C ↔ u ∈ LL F κ ∧ (a / c) • u ∈ dualL F G := by
    intro u
    simp only [C, AddSubgroup.mem_inf, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, hB]
  have h2 : ∀ x y, f (x + y) = f x * f y * g x y := by
    intro x y
    show et (a / c * QF G (x + y)) = et (a / c * QF G x) * et (a / c * QF G y) * et (a / c * BF G x y)
    rw [(hsym x y).2, show a / c * (QF G x + BF G x y + QF G y) =
      a / c * QF G x + a / c * QF G y + a / c * BF G x y by ring, het_add, het_add]
  have h3 : ∀ x y z, g (x + y) z = g x z * g y z := by
    intro x y z
    show et (a / c * BF G (x + y) z) = et (a / c * BF G x z) * et (a / c * BF G y z)
    rw [hadd, mul_add, het_add]
  have h4 : ∀ (n : ℤ) x, f (n • x) = f x ^ (n ^ 2) := by
    intro n x
    show et (a / c * QF G (n • x)) = et (a / c * QF G x) ^ (n ^ 2)
    rw [← Int.cast_smul_eq_zsmul F n x, (hlin (n : F) x x).2.1, ← GaussPow.et_zsmul (n ^ 2)]
    congr 1
    push_cast
    ring
  have h5 : ∀ x ∈ aL κ (1 : F), ∀ l ∈ aL κ c, f (x + l) = f x := by
    intro x hx l hl
    obtain ⟨l', hl', rfl⟩ := (haL c l).mp hl
    rw [hB] at hx
    show et (a / c * QF G (x + c • l')) = et (a / c * QF G x)
    rw [(hsym x _).2, (hsym x (c • l')).1, (hlin c l' x).1, (hlin c l' l').2.1]
    have e1 : a / c * (c * BF G l' x) = a * BF G l' x := by
      rw [← mul_assoc, div_mul_cancel₀ a hc0]
    have e2 : a / c * (c ^ 2 * QF G l') = a * c * QF G l' := by
      rw [← mul_assoc, pow_two, ← mul_assoc, div_mul_cancel₀ a hc0]
    rw [mul_add, mul_add, e1, e2, add_assoc, het_add,
      hetI _ ((ha.mul ((hint l' hl').2 x hx)).add ((ha.mul hcI).mul (hint l' hl').1)), mul_one]
  have h6 : ∀ u ∈ aL κ (1 : F), (∀ x ∈ aL κ (1 : F), g u x = 1) ↔ u ∈ C := by
    intro u hu
    rw [hB] at hu
    rw [hCmem]
    constructor
    · intro hg
      refine ⟨hu, ?_⟩
      rw [hdualmem]
      intro l hl
      have := hg l ((hB l).mpr hl)
      rw [(hlin (a / c) u l).1]
      exact (het_one _).mp this
    · rintro ⟨-, hd'⟩ x hx
      rw [hB] at hx
      show et (a / c * BF G u x) = 1
      rw [het_one, ← (hlin (a / c) u x).1]
      exact (hdualmem _).mp hd' x hx
  have h7 : ∀ u ∈ C, f u = 1 := by
    intro u hu
    obtain ⟨huL, hud⟩ := (hCmem u).mp hu
    obtain ⟨-, hNQ⟩ := hdual _ hud
    rw [(hlin (a / c) u u).2.1] at hNQ
    show et (a / c * QF G u) = 1
    apply hetI
    have key : a / c * QF G u =
        d * ((c / N) * ((N : F) * ((a / c) ^ 2 * QF G u))) - a * b * QF G u := by
      have e : a / c * QF G u = (a / c * QF G u) * (a * d - b * c) := by rw [hadbc, mul_one]
      rw [e]
      field_simp
    rw [key]
    exact (hd.mul (hcN.mul hNQ)).sub ((ha.mul hb).mul (hint u huL).1)
  have hCB : C ≤ aL κ (1 : F) := inf_le_left
  have hAC : aL κ c ≤ C := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := (haL c x).mp hx
    rw [hCmem]
    refine ⟨hsmulL c hcI l hl, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hc0]
    exact hLd (hsmulL a ha l hl)
  have hbij := GaussPow.reps_bij hT
  haveI : Finite (aL κ (1 : F) ⧸ (aL κ c).addSubgroupOf (aL κ (1 : F))) := Finite.of_surjective _ hbij.2
  letI : Fintype (aL κ (1 : F) ⧸ (aL κ c).addSubgroupOf (aL κ (1 : F))) := Fintype.ofFinite _
  have hcardT : Fintype.card (aL κ (1 : F) ⧸ (aL κ c).addSubgroupOf (aL κ (1 : F))) = T.card := by
    rw [GaussPow.reps_card hT, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  have hnA : ∀ x ∈ aL κ (1 : F), (T.card : ℤ) • x ∈ aL κ c := by
    intro x hx
    have h0 : Fintype.card (aL κ (1 : F) ⧸ (aL κ c).addSubgroupOf (aL κ (1 : F))) •
        (QuotientAddGroup.mk (⟨x, hx⟩ : aL κ (1 : F)) :
          aL κ (1 : F) ⧸ (aL κ c).addSubgroupOf (aL κ (1 : F))) = 0 := card_nsmul_eq_zero
    rw [hcardT, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at h0
    rw [natCast_zsmul]
    simpa using h0
  have hTpos : 0 < T.card := by
    obtain ⟨y, ⟨hy, -⟩, -⟩ := hT.2 0 (zero_mem _)
    exact Finset.card_pos.mpr ⟨y, hy⟩
  have h1 : ∀ x ∈ aL κ (1 : F), f x ^ (T.card ^ 2) = 1 := by
    intro x hx
    have e1 := h4 (T.card : ℤ) x
    have e2 : f ((T.card : ℤ) • x) = 1 := by
      have := h5 0 (zero_mem _) _ (hnA x hx)
      rw [zero_add] at this
      rw [this]
      show et (a / c * QF G 0) = 1
      rw [hQ0, mul_zero]
      exact hetI 0 isIntegral_zero
    rw [e2] at e1
    rw [← zpow_natCast]
    push_cast
    exact e1.symm
  have hmain := GaussPow.gauss_reps hT hAC hCB f g (T.card ^ 2) (by positivity) h1 h2 h3 h4 h5 h6 h7
  let φc : (κ → F) →+ (κ → F) := DistribMulAction.toAddMonoidHom (κ → F) c⁻¹
  have hAeq : aL κ c = (LL F κ).comap φc := by
    ext x
    rw [haL, AddSubgroup.mem_comap]
    simp only [φc, DistribMulAction.toAddMonoidHom_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · intro hx
      exact ⟨c⁻¹ • x, hx, by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]⟩
  have hdeq : C.map φc = dualL F G := by
    ext y
    rw [AddSubgroup.mem_map]
    simp only [φc, DistribMulAction.toAddMonoidHom_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨huL, hud⟩ := (hCmem u).mp hu
      have hs : c⁻¹ = d * (a / c) - b := by
        calc c⁻¹ = (a * d - b * c) * c⁻¹ := by rw [hadbc, one_mul]
          _ = d * (a / c) - b * (c * c⁻¹) := by ring
          _ = d * (a / c) - b := by rw [mul_inv_cancel₀ hc0, mul_one]
      rw [hs, sub_smul, mul_smul]
      exact sub_mem (hdsmul d _ hd hud) (hLd (hsmulL b hb u huL))
    · intro hy
      refine ⟨c • y, (hCmem _).mpr ⟨?_, ?_⟩, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
      · have e : c • y = (c / N) • ((N : F) • y) := by rw [smul_smul, div_mul_cancel₀ c hN0]
        rw [e]
        exact hsmulL _ hcN _ (hdual y hy).1
      · rw [smul_smul, div_mul_cancel₀ a hc0]
        exact hdsmul a y ha hy
  have hrel : (aL κ c).relIndex C = (LL F κ).relIndex (dualL F G) := by
    rw [hAeq, AddSubgroup.relIndex_comap, hdeq]
  obtain ⟨T', hT', -, -, hT'c⟩ := GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm F κ c 1 hc0 one_ne_zero (by simpa using hcI)
  have hTc : (T.card : ℚ) = |Algebra.norm ℚ c| ^ (2 * k) := by
    rw [GaussPow.reps_card hT, ← GaussPow.reps_card hT', hT'c, div_one, hk]
  have hdet : G.det ≠ 0 := by
    intro h0
    have := hG.1.det_pos
    rw [← Int.cast_det, h0, Int.cast_zero] at this
    exact lt_irrefl _ this
  have ht0 : (t : ℂ) ≠ 0 := by
    have : t ≠ 0 := by
      rintro rfl
      apply hdet
      rw [ht]
      simp
    exact_mod_cast this
  have hn0 : ((Algebra.norm ℚ c : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast Algebra.norm_ne_zero_iff.mpr hc0
  have hδ0 : (((discr F).natAbs : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)
  have hRC : ((LL F κ).relIndex (dualL F G) : ℂ) =
      (((discr F).natAbs : ℕ) : ℂ) ^ (2 * k) * (t : ℂ) ^ (2 * Module.finrank ℚ F) := by
    have h' : (((LL F κ).relIndex (dualL F G) : ℕ) : ℤ) =
        (((discr F).natAbs : ℕ) : ℤ) ^ (2 * k) * (t : ℤ) ^ (2 * Module.finrank ℚ F) := by
      rw [hidx, hk, ht, ← pow_mul]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h'
  have hTC : (T.card : ℂ) = (((|Algebra.norm ℚ c| ^ (2 * k) : ℚ)) : ℂ) := by
    rw [← hTc, Rat.cast_natCast]
  have hq4 : ((((|Algebra.norm ℚ c| ^ (2 * k) : ℚ)) : ℂ)) ^ 4 =
      ((Algebra.norm ℚ c : ℚ) : ℂ) ^ (2 * k * 4) := by
    rw [← Rat.cast_pow, ← pow_mul, Even.pow_abs ⟨4 * k, by ring⟩, Rat.cast_pow]
  have hI : ((-Complex.I) ^ (k * Module.finrank ℚ F)) ^ 8 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul,
      show (-Complex.I) ^ 8 = 1 by
        rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, neg_sq, Complex.I_sq]; norm_num,
      one_pow]
  rw [mul_pow]
  show wC k t c c ^ 8 * (∑ x ∈ T, f x) ^ 8 = 1
  rw [hmain, hrel, hTC, hRC, mul_pow, hq4]
  unfold wC
  rw [div_pow, mul_pow, hI, one_mul]
  field_simp
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_normalized_gaussSum_eighth_root : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → (wC k t c c * ∑ x ∈ T, et (a / c * QF G x)) ^ 8 = 1 := by
  first | exact @GlobalTheory.HilbertThetaSeries.gaussSum_pow_eight | exact GlobalTheory.HilbertThetaSeries.gaussSum_pow_eight | (intros; apply GlobalTheory.HilbertThetaSeries.gaussSum_pow_eight <;> assumption)
