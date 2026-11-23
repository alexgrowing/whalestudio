import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

namespace GlobalTheory.DecompFixed

open Pointwise

variable (A : Type) {B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

def decompFixed (q : Ideal B) : Subalgebra A B where
  carrier := {x | ∀ g : G, g • q = q → g • x = x}
  mul_mem' {x y} hx hy g hg := by rw [smul_mul', hx g hg, hy g hg]
  add_mem' {x y} hx hy g hg := by rw [smul_add, hx g hg, hy g hg]
  algebraMap_mem' a g _ := by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem mem_decompFixed {q : Ideal B} {x : B} :
    x ∈ decompFixed A G q ↔ ∀ g : G, g • q = q → g • x = x := Iff.rfl

def satIdeal (q : Ideal B) [q.IsPrime] (J : Ideal (decompFixed A G q)) :
    Ideal (decompFixed A G q) where
  carrier := {y | ∃ b : decompFixed A G q, (b : B) ∉ q ∧ b * y ∈ J}
  add_mem' {x y} := by
    rintro ⟨b, hb, hbx⟩ ⟨c, hc, hcy⟩
    refine ⟨b * c, ?_, ?_⟩
    · simpa using (Ideal.IsPrime.mul_notMem inferInstance hb hc)
    · have : b * c * (x + y) = c * (b * x) + b * (c * y) := by ring
      rw [this]
      exact J.add_mem (J.mul_mem_left _ hbx) (J.mul_mem_left _ hcy)
  zero_mem' := ⟨1, by simpa using (Ideal.IsPrime.ne_top inferInstance : q ≠ ⊤) ∘
    (Ideal.eq_top_iff_one q).2, by simp⟩
  smul_mem' c {y} := by
    rintro ⟨b, hb, hby⟩
    refine ⟨b, hb, ?_⟩
    have : b * (c • y) = c * (b * y) := by rw [smul_eq_mul]; ring
    rw [this]
    exact J.mul_mem_left _ hby

theorem mem_satIdeal {q : Ideal B} [q.IsPrime] {J : Ideal (decompFixed A G q)}
    {y : decompFixed A G q} :
    y ∈ satIdeal A G q J ↔ ∃ b : decompFixed A G q, (b : B) ∉ q ∧ b * y ∈ J := Iff.rfl

end GlobalTheory.DecompFixed

namespace GlobalTheory.DecompFixed

open Pointwise IsLocalRing

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B]

theorem exists_unit (q : Ideal B) [q.IsMaximal] :
    ∃ u : B, (∀ g : G, g • q = q → g • u = u) ∧ u - 1 ∈ q ∧
      ∀ g : G, g • q ≠ q → g • u ∈ q := by
  classical
  cases nonempty_fintype G
  set P : Ideal B := Finset.inf (Finset.univ.filter (fun g : G => g • q ≠ q)) (fun g => g • q)
  have h1 : ¬ P ≤ q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨y0, hyP, hyq⟩ := SetLike.not_le_iff_exists.mp h1
  obtain ⟨c, i, hi, hci⟩ := Ideal.IsMaximal.exists_inv (inferInstance : q.IsMaximal) hyq
  set y := c * y0 with hy
  have hyP' : ∀ g : G, g • q ≠ q → y ∈ g • q := fun g hg =>
    Ideal.mul_mem_left _ c
      ((Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) : P ≤ g • q) hyP)
  have hy1 : y - 1 ∈ q := by
    have : y - 1 = -i := by rw [hy, ← hci]; ring
    rw [this]; exact q.neg_mem hi
  set D := Finset.univ.filter (fun g : G => g • q = q) with hD
  refine ⟨∏ g ∈ D, g • y, ?_, ?_, ?_⟩
  · intro h hh
    rw [Finset.smul_prod']
    refine Finset.prod_nbij' (fun g => h * g) (fun g => h⁻¹ * g) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      simp only [hD, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [mul_smul, hg, hh]
    · intro g hg
      simp only [hD, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [mul_smul, hg, inv_smul_eq_iff, hh]
    · intro g _; simp
    · intro g _; simp
    · intro g _; rw [mul_smul]
  · rw [← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one (fun g hg => ?_)
    have hg' : g • q = q := (Finset.mem_filter.mp hg).2
    rw [← map_one (Ideal.Quotient.mk q), Ideal.Quotient.eq]
    have : g • y - 1 = g • (y - 1) := by rw [smul_sub, smul_one]
    rw [this, ← hg']
    exact Ideal.smul_mem_pointwise_smul_iff.mpr hy1
  · intro g hg
    rw [Finset.smul_prod']
    have h1D : (1 : G) ∈ D := by simp [hD]
    refine Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ h1D) ?_
    rw [one_smul]
    have hgi : g⁻¹ • q ≠ q := fun h => hg (by nth_rewrite 1 [← h]; exact smul_inv_smul g q)
    have := hyP' g⁻¹ hgi
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv] at this
    exact this

end GlobalTheory.DecompFixed

namespace GlobalTheory.DecompFixed

open Pointwise IsLocalRing

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B]

theorem orbitSum_smul [Fintype G] [DecidableEq B] (w : B) (g : G) :
    g • (∑ z ∈ Finset.univ.image (fun h : G => h • w), z) =
      ∑ z ∈ Finset.univ.image (fun h : G => h • w), z := by
  rw [Finset.smul_sum]
  have hO : (Finset.univ.image (fun h : G => h • w)).image (fun z => g • z) =
      Finset.univ.image (fun h : G => h • w) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨g * h, mul_smul g h w⟩
    · rintro ⟨h, rfl⟩; exact ⟨g⁻¹ * h, by rw [mul_smul, smul_inv_smul]⟩
  conv_rhs => rw [← hO]
  rw [Finset.sum_image (fun a _ b _ h => MulAction.injective g h)]

theorem exists_sub_mem [Algebra.IsInvariant A B G] (q : Ideal B) [q.IsMaximal] (u : B)
    (hu : ∀ g : G, g • q = q → g • u = u) (hu1 : u - 1 ∈ q)
    (hu2 : ∀ g : G, g • q ≠ q → g • u ∈ q)
    (x : B) (hx : ∀ g : G, g • q = q → g • x = x) : ∃ a : A, x - algebraMap A B a ∈ q := by
  classical
  cases nonempty_fintype G
  have hwfix : ∀ g : G, g • q = q → g • (u * x) = u * x := fun g hg => by
    rw [smul_mul', hu g hg, hx g hg]
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) _
    (fun g => orbitSum_smul (u * x) g)
  refine ⟨a, ?_⟩
  rw [ha]
  have hwO : u * x ∈ Finset.univ.image (fun h : G => h • (u * x)) :=
    Finset.mem_image.2 ⟨1, Finset.mem_univ _, one_smul _ _⟩
  rw [← Finset.add_sum_erase _ (fun z => z) hwO]
  have h1 : x - u * x ∈ q := by
    have : x - u * x = -((u - 1) * x) := by ring
    rw [this]; exact q.neg_mem (q.mul_mem_right _ hu1)
  have h2 : ∑ z ∈ (Finset.univ.image (fun h : G => h • (u * x))).erase (u * x), z ∈ q := by
    refine Ideal.sum_mem _ (fun z hz => ?_)
    obtain ⟨hzw, hzO⟩ := Finset.mem_erase.1 hz
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.1 hzO
    by_cases hg : g • q = q
    · exact absurd (hwfix g hg) hzw
    · rw [smul_mul']; exact q.mul_mem_right _ (hu2 g hg)
  have : x - (u * x + ∑ z ∈ (Finset.univ.image (fun h : G => h • (u * x))).erase (u * x), z) =
      (x - u * x) - ∑ z ∈ (Finset.univ.image (fun h : G => h • (u * x))).erase (u * x), z := by
    ring
  rw [this]; exact q.sub_mem h1 h2

end GlobalTheory.DecompFixed

namespace GlobalTheory.DecompFixed

open Pointwise IsLocalRing Polynomial

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B]

theorem image_smul_orbit {α : Type} [MulAction G α] [Fintype G] [DecidableEq α] (w : α) (g : G) :
    (Finset.univ.image (fun h : G => h • w)).image (fun z => g • z) =
      Finset.univ.image (fun h : G => h • w) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨g * h, mul_smul g h w⟩
  · rintro ⟨h, rfl⟩; exact ⟨g⁻¹ * h, by rw [mul_smul, smul_inv_smul]⟩

theorem prod_orbit_smul {α : Type} [MulAction G α] [Fintype G] [DecidableEq α] (w : α)
    (φ : α → B) (hφ : ∀ (g : G) z, φ (g • z) = g • φ z) (g : G) :
    g • (∏ z ∈ Finset.univ.image (fun h : G => h • w), (X - C (φ z))) =
      ∏ z ∈ Finset.univ.image (fun h : G => h • w), (X - C (φ z)) := by
  rw [Finset.smul_prod']
  simp_rw [smul_sub, smul_X, smul_C, ← hφ]
  conv_rhs => rw [← image_smul_orbit w g]
  rw [Finset.prod_image (fun a _ b _ h => MulAction.injective g h)]

theorem exists_lift [Algebra.IsInvariant A B G] (P : B[X]) (hP : ∀ g : G, g • P = P) :
    ∃ p : A[X], p.map (algebraMap A B) = P := by
  have : P ∈ Polynomial.lifts (algebraMap A B) := (Polynomial.lifts_iff_coeff_lifts P).2 fun n =>
    Algebra.IsInvariant.isInvariant (G := G) _ (fun g => by rw [← Polynomial.coeff_smul, hP g])
  obtain ⟨p, hp⟩ := this
  exact ⟨p, by simpa using hp⟩

theorem eval_map_coe (q : Ideal B) (p : A[X]) (r : decompFixed A G q) :
    (((p.map (algebraMap A (decompFixed A G q))).eval r : decompFixed A G q) : B) =
      (p.map (algebraMap A B)).eval (r : B) := by
  rw [Polynomial.eval_map, Polynomial.eval_map]
  exact Polynomial.hom_eval₂ p (algebraMap A (decompFixed A G q))
    ((decompFixed A G q).val : decompFixed A G q →+* B) r

end GlobalTheory.DecompFixed

namespace GlobalTheory.DecompFixed

open Pointwise IsLocalRing Polynomial

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B]

theorem exists_mul_mem_map [IsLocalRing A] [Algebra.IsInvariant A B G] (q : Ideal B)
    [q.IsMaximal] (u : B)
    (hu : ∀ g : G, g • q = q → g • u = u) (hu1 : u - 1 ∈ q)
    (hu2 : ∀ g : G, g • q ≠ q → g • u ∈ q)
    (x : decompFixed A G q) (hxq : (x : B) ∈ q) :
    ∃ b : decompFixed A G q, (b : B) ∉ q ∧
      b * x ∈ (maximalIdeal A).map (algebraMap A (decompFixed A G q)) := by
  classical
  cases nonempty_fintype G
  have hqtop : q ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have hxfix : ∀ g : G, g • q = q → g • (x : B) = x := (mem_decompFixed A G).1 x.2
  let uR : decompFixed A G q := ⟨u, (mem_decompFixed A G).2 hu⟩
  obtain ⟨v, hvdef⟩ : ∃ v : B, v = u * (1 + x) := ⟨_, rfl⟩
  have hv : ∀ g : G, g • q = q → g • v = v := fun g hg => by
    rw [hvdef, smul_mul', smul_add, smul_one, hu g hg, hxfix g hg]
  obtain ⟨S, hS⟩ : ∃ S : Finset (B × B), S = Finset.univ.image (fun h : G => h • (u, v)) :=
    ⟨_, rfl⟩
  have huv : (u, v) ∈ S := hS ▸ Finset.mem_image.2 ⟨1, Finset.mem_univ _, one_smul _ _⟩
  have hmem : ∀ z ∈ S, z ≠ (u, v) → z.1 ∈ q ∧ z.2 ∈ q := by
    intro z hz hne
    rw [hS] at hz
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.1 hz
    by_cases hg : g • q = q
    · exact absurd (by rw [Prod.smul_mk, hu g hg, hv g hg]) hne
    · refine ⟨hu2 g hg, ?_⟩
      show g • v ∈ q
      rw [hvdef, smul_mul']
      exact q.mul_mem_right _ (hu2 g hg)
  have hcong : ∀ z ∈ S, z.1 - z.2 ∈ q := by
    intro z hz
    by_cases hne : z = (u, v)
    · subst hne
      show u - v ∈ q
      have : u - v = -(u * x) := by rw [hvdef]; ring
      rw [this]; exact q.neg_mem (q.mul_mem_left _ hxq)
    · obtain ⟨h1, h2⟩ := hmem z hz hne; exact q.sub_mem h1 h2
  obtain ⟨Pu, hPu⟩ : ∃ P : B[X], P = ∏ z ∈ S, (X - C z.1) := ⟨_, rfl⟩
  obtain ⟨Pv, hPv⟩ : ∃ P : B[X], P = ∏ z ∈ S, (X - C z.2) := ⟨_, rfl⟩
  obtain ⟨pu, hpu⟩ := exists_lift (A := A) (G := G) Pu (by
    rw [hPu, hS]; exact prod_orbit_smul (u, v) Prod.fst (fun _ _ => rfl))
  obtain ⟨pv, hpv⟩ := exists_lift (A := A) (G := G) Pv (by
    rw [hPv, hS]; exact prod_orbit_smul (u, v) Prod.snd (fun _ _ => rfl))
  have hcoeff : ∀ n, (pu - pv).coeff n ∈ maximalIdeal A := by
    intro n
    have hq : (Pu - Pv).coeff n ∈ q := by
      have hmap : (Pu - Pv).map (Ideal.Quotient.mk q) = 0 := by
        rw [Polynomial.map_sub, sub_eq_zero, hPu, hPv, Polynomial.map_prod, Polynomial.map_prod]
        refine Finset.prod_congr rfl (fun z hz => ?_)
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rw [Ideal.Quotient.eq.2 (hcong z hz)]
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, hmap, Polynomial.coeff_zero]
    rw [← hpu, ← hpv, ← Polynomial.map_sub, Polynomial.coeff_map] at hq
    by_contra hn
    have hunit : IsUnit ((pu - pv).coeff n) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
    exact hqtop (Ideal.eq_top_of_isUnit_mem q hq (hunit.map _))
  have hPu_u : Pu.eval u = 0 := by
    rw [hPu, Polynomial.eval_prod]
    exact Finset.prod_eq_zero huv (by simp)
  have hPv_v : Pv.eval v = 0 := by
    rw [hPv, Polynomial.eval_prod]
    exact Finset.prod_eq_zero huv (by simp)
  have hder : Pu.derivative.eval u - 1 ∈ q := by
    rw [hPu, ← Finset.mul_prod_erase S (fun z => X - C z.1) huv, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_prod]
    rw [← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one (fun z hz => ?_)
    obtain ⟨hne, hzS⟩ := Finset.mem_erase.1 hz
    rw [← map_one (Ideal.Quotient.mk q), Ideal.Quotient.eq]
    have : u - z.1 - 1 = (u - 1) - z.1 := by ring
    rw [this]; exact q.sub_mem hu1 (hmem z hzS hne).1
  set fu : (decompFixed A G q)[X] := pu.map (algebraMap A (decompFixed A G q)) with hfu
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion fu uR (uR * x)
  have hfu0 : fu.eval uR = 0 := Subtype.ext (by
    rw [hfu, eval_map_coe, hpu]; simpa using hPu_u)
  have hfud : ((fu.derivative.eval uR : decompFixed A G q) : B) = Pu.derivative.eval u := by
    rw [hfu, Polynomial.derivative_map, eval_map_coe, ← Polynomial.derivative_map, hpu]
  have hfuv : fu.eval (uR + uR * x) ∈ (maximalIdeal A).map (algebraMap A (decompFixed A G q)) := by
    have h0 : (pv.map (algebraMap A (decompFixed A G q))).eval (uR + uR * x) = 0 :=
      Subtype.ext (by
        rw [eval_map_coe, hpv]
        have : ((uR + uR * x : decompFixed A G q) : B) = v := by
          rw [hvdef]; push_cast; ring
        rw [this, hPv_v]; rfl)
    have : fu.eval (uR + uR * x) =
        ((pu - pv).map (algebraMap A (decompFixed A G q))).eval (uR + uR * x) := by
      rw [Polynomial.map_sub, Polynomial.eval_sub, h0, sub_zero]
    rw [this, Polynomial.eval_eq_sum_range]
    refine Ideal.sum_mem _ (fun n _ => Ideal.mul_mem_right _ _ ?_)
    rw [Polynomial.coeff_map]
    exact Ideal.mem_map_of_mem _ (hcoeff n)
  refine ⟨uR * (fu.derivative.eval uR + k * (uR * x)), ?_, ?_⟩
  · intro hbq
    apply hqtop
    rw [Ideal.eq_top_iff_one]
    have hb : ((uR * (fu.derivative.eval uR + k * (uR * x)) : decompFixed A G q) : B) =
        u * (Pu.derivative.eval u + k * (u * x)) := by
      push_cast; rw [hfud]
    rw [hb] at hbq
    have h1 : (1 : B) = u * (Pu.derivative.eval u + k * (u * x)) -
        ((u - 1) * (Pu.derivative.eval u + k * (u * x)) + (Pu.derivative.eval u - 1) +
          k * (u * x)) := by ring
    rw [h1]
    refine q.sub_mem hbq (q.add_mem (q.add_mem (q.mul_mem_right _ hu1) hder) ?_)
    exact q.mul_mem_left _ (q.mul_mem_left _ hxq)
  · have : uR * (fu.derivative.eval uR + k * (uR * x)) * x = fu.eval (uR + uR * x) := by
      rw [hk, hfu0]; ring
    rw [this]; exact hfuv

end GlobalTheory.DecompFixed

namespace GlobalTheory.DecompFixed

open Pointwise IsLocalRing

variable {A B G : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B]

theorem exists_approx [IsLocalRing A] [Algebra.IsInvariant A B G] (q : Ideal B) [q.IsMaximal]
    (f : B) (hf : ∀ g : G, g • q = q → g • f = f) (e : ℕ) :
    ∃ (a : A) (b : B), b ∉ q ∧
      b * (f - algebraMap A B a) ∈ (maximalIdeal A ^ e).map (algebraMap A B) := by
  classical
  set R := decompFixed A G q
  set I : Ideal R := (maximalIdeal A).map (algebraMap A R) with hI
  let T : ℕ → Ideal R := fun n => satIdeal A G q (I ^ n)
  obtain ⟨u, hu, hu1, hu2⟩ := exists_unit (G := G) q
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hcomap : q.comap (algebraMap A B) = maximalIdeal A := by
    haveI : (q.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
    exact IsLocalRing.eq_maximalIdeal this
  have hm : ∀ a ∈ maximalIdeal A, algebraMap A B a ∈ q := fun a ha => by
    rw [← hcomap] at ha; exact ha

  have hIq : ∀ y ∈ I, (y : B) ∈ q := by
    intro y hy
    have : I ≤ q.comap (decompFixed A G q).val := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro a ha
      exact hm a ha
    exact this hy
  have hIpow : ∀ n, I ^ (n + 1) ≤ I := fun n => Ideal.pow_le_self (Nat.succ_ne_zero n)

  have stepA : ∀ r : R, ∃ a : A, r - algebraMap A R a ∈ T 1 := by
    intro r
    obtain ⟨a, ha⟩ := exists_sub_mem (A := A) (G := G) q u hu hu1 hu2 (r : B) r.2
    obtain ⟨b, hb, hbr⟩ := exists_mul_mem_map q u hu hu1 hu2 (r - algebraMap A R a) (by simpa using ha)
    exact ⟨a, b, hb, by simpa using hbr⟩

  have stepB : ∀ i j (y z : R), y ∈ T i → z ∈ T j → y * z ∈ T (i + j) := by
    rintro i j y z ⟨b, hb, hby⟩ ⟨c, hc, hcz⟩
    refine ⟨b * c, ?_, ?_⟩
    · simpa using (Ideal.IsPrime.mul_notMem inferInstance hb hc)
    · have : b * c * (y * z) = (b * y) * (c * z) := by ring
      rw [this, pow_add]
      exact Ideal.mul_mem_mul hby hcz
  have hTle : ∀ n (y : R), y ∈ I ^ n → y ∈ T n := fun n y hy => ⟨1, by simpa using
    (Ideal.IsPrime.ne_top inferInstance : q ≠ ⊤) ∘ (Ideal.eq_top_iff_one q).2, by simpa using hy⟩

  have stepC : ∀ n (y : R), y ∈ I ^ n → ∃ c ∈ maximalIdeal A ^ n, y - algebraMap A R c ∈ T (n + 1) := by
    intro n y hy
    rw [hI, ← Ideal.map_pow, Ideal.map] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨c, hc, by simp⟩
    | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      refine ⟨c + d, Ideal.add_mem _ hc hd, ?_⟩
      have : x + y - algebraMap A R (c + d) = (x - algebraMap A R c) + (y - algebraMap A R d) := by
        rw [map_add]; ring
      rw [this]; exact Ideal.add_mem _ hxc hyd
    | smul r x _ hx =>
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨a, ha⟩ := stepA r
      refine ⟨c * a, Ideal.mul_mem_right _ _ hc, ?_⟩
      have hcI : algebraMap A R c ∈ T n := hTle n _ (by
        rw [hI, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc)
      have : r • x - algebraMap A R (c * a) =
          r * (x - algebraMap A R c) + algebraMap A R c * (r - algebraMap A R a) := by
        rw [smul_eq_mul, map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxc) (stepB n 1 _ _ hcI ha)

  have stepD : ∀ n (y : R), ∃ a : A, y - algebraMap A R a ∈ T n := by
    intro n
    induction n with
    | zero => exact fun y => ⟨0, hTle 0 _ (by simp)⟩
    | succ n ih =>
      intro y
      obtain ⟨a, b, hb, hby⟩ := ih y
      obtain ⟨c, hc, hcy⟩ := stepC n _ hby
      obtain ⟨β, hβ⟩ := stepA b
      have hβu : IsUnit β := by
        by_contra hβn
        have hβm : β ∈ maximalIdeal A := hβn
        obtain ⟨b', hb', hb'β⟩ := hβ
        have h1 : ((b' * (b - algebraMap A R β) : R) : B) ∈ q := hIq _ (by simpa using hb'β)
        have h2 : ((b - algebraMap A R β : R) : B) ∈ q :=
          ((Ideal.IsPrime.mem_or_mem inferInstance (by simpa using h1)).resolve_left hb')
        apply hb
        have h3 : (b : B) = ((b - algebraMap A R β : R) : B) + algebraMap A B β := by simp
        rw [h3]; exact Ideal.add_mem _ h2 (hm β hβm)
      obtain ⟨γ, hγ⟩ : ∃ γ : A, γ * β = 1 := ⟨(hβu.unit⁻¹ : Aˣ), hβu.val_inv_mul⟩
      refine ⟨a + γ * c, ?_⟩
      have key : y - algebraMap A R (a + γ * c) = algebraMap A R γ *
          ((-(b - algebraMap A R β)) * (y - algebraMap A R a) +
            (b * (y - algebraMap A R a) - algebraMap A R c)) := by
        have : algebraMap A R γ * algebraMap A R β = 1 := by rw [← map_mul, hγ, map_one]
        rw [map_add, map_mul]
        linear_combination (-(y - algebraMap A R a)) * this
      rw [key]
      refine Ideal.mul_mem_left _ _ (Ideal.add_mem _ ?_ hcy)
      have := stepB 1 n _ _ ((T 1).neg_mem hβ) ⟨b, hb, hby⟩
      rwa [add_comm] at this
  obtain ⟨a, b, hb, hbf⟩ := stepD e ⟨f, hf⟩
  refine ⟨a, b, hb, ?_⟩
  have hmap : Ideal.map (R.val : R →+* B) (I ^ e) = (maximalIdeal A ^ e).map (algebraMap A B) := by
    rw [hI, ← Ideal.map_pow, Ideal.map_map]; rfl
  rw [← hmap]
  simpa using Ideal.mem_map_of_mem (R.val : R →+* B) hbf

end GlobalTheory.DecompFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DecompFixed

theorem exists_approx_integralClosure : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L] (q : Ideal (integralClosure A L)) [q.IsMaximal] (f : integralClosure A L), (∀ σ : L ≃ₐ[K] L, (∀ x y : integralClosure A L, (y : L) = σ x → (x ∈ q ↔ y ∈ q)) → σ f = f) → ∀ e : ℕ, ∃ (a : A) (b : integralClosure A L), b ∉ q ∧ b * (f - algebraMap A _ a) ∈ (maximalIdeal A ^ e).map (algebraMap A (integralClosure A L)) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ _ _ q _ f hf e
  letI : SMulCommClass (L ≃ₐ[K] L) A L := ⟨fun σ a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A K L, AlgEquiv.commutes]⟩
  haveI : Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) := ⟨fun b hb => by
    have hL : ∀ σ : L ≃ₐ[K] L, σ (b : L) = b := fun σ => congrArg Subtype.val (hb σ)
    have hbot : (b : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).2 hL
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hbot
    have hint : IsIntegral A k := by
      have h1 : IsIntegral A (algebraMap K L k) := hk ▸ b.2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L)
        (algebraMap K L).injective).1 h1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨a, Subtype.ext ?_⟩
    rw [← hk, ← ha]
    simp [IsScalarTower.algebraMap_apply A K L]⟩
  refine exists_approx (G := L ≃ₐ[K] L) q f (fun g hg => Subtype.ext ?_) e
  refine hf g (fun x y hxy => ?_)
  have hy : y = g • x := Subtype.ext (by simpa [AlgEquiv.smul_def] using hxy)
  rw [hy]
  conv_rhs => rw [← hg]
  exact (Ideal.smul_mem_pointwise_smul_iff).symm

end GlobalTheory.DecompFixed
