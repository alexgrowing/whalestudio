import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

theorem exists_full_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
    (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
    ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P _ K b b' hb h
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let ι : P.R.B →+* FractionRing P.R.B := algebraMap P.R.B (FractionRing P.R.B)
  have hι : Function.Injective ι := IsFractionRing.injective P.R.B (FractionRing P.R.B)
  let e : GQ l → FractionRing P.R.B ≃+* FractionRing P.R.B := fun g =>
    IsFractionRing.ringEquivOfRingEquiv (A := P.R.B) (B := P.R.B) (P.actQ g).toRingEquiv
  have he : ∀ g z, e g (ι z) = ι (P.actQ g z) := fun g z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  have hmul : ∀ s g z, e s (e g z) = e (s * g) z := by
    intro s g
    have : (e s).toRingHom.comp (e g).toRingHom = (e (s * g)).toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors P.R.B)
      ext z
      show e s (e g (ι z)) = e (s * g) (ι z)
      rw [he, he, he, map_mul, AlgEquiv.mul_apply]
    intro z
    exact RingHom.congr_fun this z
  have hne : ∀ g (z : P.R.B), z ≠ 0 → ι (P.actQ g z) ≠ 0 := fun g z hz =>
    (map_ne_zero_iff ι hι).2 ((map_ne_zero_iff _ (P.actQ g).injective).2 hz)
  let T : GQ l → FractionRing P.R.B := fun g => ι ((kummer P g : ℚ_[l]) • P.tB)
  have hT : ∀ s g, e s (T g) = T (s * g) - T s := by
    intro s g
    simp only [T, he, map_smul, localPrime_galoisAction_periodT, kummer_mul, smul_smul, add_smul, map_add]
    rw [mul_comm]; abel
  let f : FractionRing P.R.B := ι b' / ι b
  have hb0 : ι b ≠ 0 := (map_ne_zero_iff ι hι).2 hb
  have hf : ∀ g ∈ GK K, e g f - f = T g := by
    intro g hg
    have h1 := congrArg ι (h g hg)
    simp only [map_sub, map_mul] at h1
    have h2 := hne g b hb
    simp only [f, map_div₀, he]
    field_simp
    linear_combination h1
  let Fn : GQ l → FractionRing P.R.B := fun g => e g f - T g
  have h1 : ∀ s g, e s (Fn g) = Fn (s * g) + T s := by
    intro s g
    simp only [Fn, map_sub, hmul, hT]
    abel
  have h2 : ∀ g (k : ↥(GK K)), Fn (g * k) = Fn g := by
    intro g k
    have e1 : Fn k = f := by simp only [Fn, ← hf k k.2]; abel
    have := h1 g k
    rw [e1] at this
    simp only [Fn] at this ⊢
    linear_combination -this
  have h3 : ∀ g, Fn (QuotientGroup.mk g : GQ l ⧸ GK K).out = Fn g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hk, h2]
  have hnB : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : P.R.B) ≠ 0 := by
    haveI := nontrivial_B P
    rw [← map_natCast (algebraMap ℚ_[l] P.R.B)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ_[l] P.R.B)).2
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff ι hι).2 hnB
  let fa : FractionRing P.R.B := ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B)⁻¹ * ∑ q : GQ l ⧸ GK K, Fn q.out
  have hfa : ∀ s, e s fa - fa = T s := by
    intro s
    have h4 : ∑ q : GQ l ⧸ GK K, Fn (s * q.out) = ∑ q : GQ l ⧸ GK K, Fn q.out :=
      Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
        rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]
    simp only [fa, map_mul, map_inv₀, map_natCast, map_sum, h1]
    rw [Finset.sum_add_distrib, h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨y, x, hx, hxy⟩ := IsFractionRing.div_surjective (A := P.R.B) fa
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  refine ⟨x, y, hx0, fun g => ?_⟩
  have hxy' : ι y / ι x = fa := hxy
  have k := hfa g
  rw [← hxy', map_div₀, he, he] at k
  have k1 := hne g x hx0
  have k2 : ι x ≠ 0 := (map_ne_zero_iff ι hι).2 hx0
  apply hι
  simp only [map_sub, map_mul]
  field_simp at k
  linear_combination k

end GlobalTheory.Pst.NoLog
