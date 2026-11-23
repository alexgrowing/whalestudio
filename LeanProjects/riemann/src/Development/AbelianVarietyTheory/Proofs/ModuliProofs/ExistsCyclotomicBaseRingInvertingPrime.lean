import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.CycBase

lemma zeta_prim {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (zeta k) k := Complex.isPrimitiveRoot_exp k hk

lemma snd_eq_zero {p k : ℕ} (hk : k ≠ 0) (hkp : k.Coprime p) (hp : p.Prime) {K : Type} [Field K]
    (f : ZP p k →+* DualNumber K) (x : ZP p k) : (f x).snd = 0 := by
  have hinv : ∀ m : ℕ, m.Coprime p → ∀ h : (m : ℂ)⁻¹ ∈ ZP p k,
      (f ⟨_, h⟩).snd = 0 ∧ (m : K) ≠ 0 := by
    intro m hm h
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp.ne_one (by simpa using hm)
    have h1 : (m : ZP p k) * ⟨_, h⟩ = 1 := by
      apply Subtype.ext
      simp [hm0]
    have h2 := congrArg f h1
    rw [map_mul, map_natCast, map_one] at h2
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.fst_one] at h3
    have hmK : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h3
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, zero_mul, add_zero,
      TrivSqZeroExt.snd_one] at h4
    exact ⟨(mul_eq_zero.mp h4).resolve_left hmK, hmK⟩
  have hkK : (k : K) ≠ 0 := (hinv k hkp (Subring.subset_closure (Or.inr ⟨k, hkp, rfl⟩))).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨m, hm, rfl⟩
    · have h1 : zetaZP p k ^ k = 1 := Subtype.ext (zeta_prim hk).pow_eq_one
      have h2 := congrArg f h1
      rw [map_pow, map_one] at h2
      have h3 := congrArg TrivSqZeroExt.fst h2
      have h4 := congrArg TrivSqZeroExt.snd h2
      rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h3
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h4
      have h5 : (f (zetaZP p k)).fst ≠ 0 := by
        intro h0
        rw [h0, zero_pow hk] at h3
        exact zero_ne_one h3
      change (f (zetaZP p k)).snd = 0
      simpa [hkK, h5] using h4
    · exact (hinv m hm _).1
  | zero => change (f 0).snd = 0; simp
  | one => change (f 1).snd = 0; simp
  | add x y hx hy ihx ihy =>
    change (f (⟨x, hx⟩ + ⟨y, hy⟩)).snd = 0
    simp only [map_add, TrivSqZeroExt.snd_add, ihx, ihy, add_zero]
  | neg x hx ihx =>
    change (f (-⟨x, hx⟩)).snd = 0
    simp only [map_neg, TrivSqZeroExt.snd_neg, ihx, neg_zero]
  | mul x y hx hy ihx ihy =>
    change (f (⟨x, hx⟩ * ⟨y, hy⟩)).snd = 0
    simp only [map_mul, DualNumber.snd_mul, ihx, ihy, mul_zero, zero_mul, add_zero]

lemma eq_constPt {p k : ℕ} (hk : k ≠ 0) (hkp : k.Coprime p) (hp : p.Prime) {K : Type} [Field K]
    (y : Sp (DualNumber K) ⟶ Sp (ZP p k)) : y = constPt y := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective y
  simp only [constPt, spMap, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [snd_eq_zero hk hkp hp f.hom x, TrivSqZeroExt.algebraMap_eq_inl]

abbrev CF (k : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zeta k}

def zF (k : ℕ) : CF k := ⟨zeta k, IntermediateField.subset_adjoin _ _ rfl⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_isPrimitiveRoot' {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta; exact Complex.isPrimitiveRoot_exp k hk

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.zF_prim {k : ℕ} (hk : k ≠ 0) :
    IsPrimitiveRoot (_root_.GlobalTheory.ZM.CycBase.zF k) k :=
  IsPrimitiveRoot.of_map_of_injective (f := (_root_.GlobalTheory.ZM.CycBase.CF k).val)
    (zeta_isPrimitiveRoot' hk) (_root_.GlobalTheory.ZM.CycBase.CF k).val.injective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.cyc {k : ℕ} [NeZero k] :
    IsCyclotomicExtension {k} ℚ (_root_.GlobalTheory.ZM.CycBase.CF k) := by
  have hζ := zeta_isPrimitiveRoot' (NeZero.ne k)
  haveI := hζ.adjoin_isCyclotomicExtension ℚ
  have h2 : (_root_.GlobalTheory.ZM.CycBase.CF k).toSubalgebra = Algebra.adjoin ℚ {_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral (NeZero.pos k)).tower_top.isAlgebraic)
  exact IsCyclotomicExtension.equiv _ _ _ (Subalgebra.equivOfEq _ _ h2).symm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
lemma _root_.GlobalTheory.ZM.CycBase.mem_ZP (p n e : ℕ) (hn : n.Prime) (a : 𝓞 (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e))) :
    ((a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : NeZero (n ^ e) := ⟨pow_ne_zero _ hn.ne_zero⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim (NeZero.ne (n ^ e))
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  obtain ⟨x, hx⟩ := hcl.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe a)
  have hax : (a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) = x := hx.symm
  rw [hax]
  obtain ⟨y, hmem⟩ := x
  change ((y : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)
  clear hx hax
  induction hmem using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
    exact Subring.subset_closure (Or.inl rfl)
  | algebraMap r =>
    simpa using intCast_mem (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) r
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | mul y z _ _ hy hz => simpa using mul_mem hy hz

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma inv_natCast_mem_ZP_of_coprime {p M m : ℕ} (hm : m.Coprime p) :
    ((m : ℂ)⁻¹) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma snd_eq_zero_of_natCast_mul_eq_one {K : Type} [Field K] {m : ℕ} {v : DualNumber K}
    (h : (m : DualNumber K) * v = 1) : v.snd = 0 ∧ (m : K) ≠ 0 := by
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp at h1 h2
  have hm : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨by simpa [hm] using h2, hm⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_mem_ZP (p M : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta M ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inl rfl)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma ringHom_ZP_pow_dualNumber_snd_eq_zero {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0) (f : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) →+* DualNumber K)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) : (f x).snd = 0 := by
  have hnK : (n : K) ≠ 0 := by
    have hmul : ((n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) * ⟨(n : ℂ)⁻¹, inv_natCast_mem_ZP_of_coprime hn⟩ = 1 := by
      apply Subtype.ext; simp [hn0]
    have := congrArg f hmul
    rw [map_mul, map_natCast, map_one] at this
    exact (snd_eq_zero_of_natCast_mul_eq_one this).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨m, hm, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      set z := f ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ with hz
      have hN : n ^ e ≠ 0 := pow_ne_zero _ hn0
      have hpow : z ^ (n ^ e) = 1 := by
        rw [hz, ← map_pow]
        have : (⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) ^ (n ^ e) = 1 :=
          Subtype.ext (by simpa using (zeta_isPrimitiveRoot' hN).pow_eq_one)
        rw [this, map_one]
      have h1 := congrArg TrivSqZeroExt.fst hpow
      have h2 := congrArg TrivSqZeroExt.snd hpow
      simp only [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h1
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h2
      have hz0 : z.fst ≠ 0 := by
        intro h0; rw [h0, zero_pow hN] at h1; exact zero_ne_one h1
      simp only [nsmul_eq_mul, smul_eq_mul] at h2
      have hNK : ((n ^ e : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hnK
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hNK
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hz0
        · exact h
    · by_cases hm0 : m = 0
      · subst hm0
        have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨0, hm, rfl⟩)⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]; rfl
      · have hmul : ((m : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) *
            ⟨(m : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)⟩ = 1 := by
          apply Subtype.ext; simp [hm0]
        have := congrArg f hmul
        rw [map_mul, map_natCast, map_one] at this
        exact (snd_eq_zero_of_natCast_mul_eq_one this).1
  | zero => rw [show (⟨0, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 from rfl, map_zero]; rfl
  | one => rw [show (⟨1, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 1 from rfl, map_one]; rfl
  | add y z hy hz ihy ihz =>
    rw [show (⟨y + z, add_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl, map_add,
      TrivSqZeroExt.snd_add, ihy, ihz, add_zero]
  | neg y hy ihy =>
    rw [show (⟨-y, neg_mem hy⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = -⟨y, hy⟩ from rfl, map_neg,
      TrivSqZeroExt.snd_neg, ihy, neg_zero]
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, mul_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
      TrivSqZeroExt.snd_mul, ihy, ihz, smul_zero, smul_zero, add_zero]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma spec_dualNumber_hom_ZP_eq_constPt {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0)
    (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e))) : y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
  conv_lhs => rw [← Spec.map_preimage y]
  conv_rhs => rw [← Spec.map_preimage y]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, ringHom_ZP_pow_dualNumber_snd_eq_zero hn hn0]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.CycBase.exists_base : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e →
    k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : _root_.GlobalTheory.ZM.TBase o k) (em : o →+* ℂ)
      (j : o →+* _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k), _root_.GlobalTheory.ZM.ArBase em ∧ j (b.ζ : o) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP p k ∧
      (∀ x, ((j x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k) : ℂ) = em x) ∧
      ∀ (K : Type) [Field K] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k)), y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  intro n e p k hn hp hnp _ hk
  subst hk
  have hN : n ^ e ≠ 0 := pow_ne_zero _ hn.ne_zero
  haveI : NeZero (n ^ e) := ⟨hN⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  haveI : NumberField (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) :=
    IsCyclotomicExtension.numberField {n ^ e} ℚ _
  have hcop : n.Coprime p := (Nat.coprime_primes hn hp).mpr hnp
  set F := _root_.GlobalTheory.ZM.CycBase.CF (n ^ e) with hF
  obtain ⟨em, har, hcomp⟩ :=
    _root_.GlobalTheory.ZM.exists_arBase_away (F := F) F.val.toRingHom hn.ne_zero
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim hN
  have hζi := hζ.toInteger_isPrimitiveRoot
  have hpos : 0 < n ^ e := Nat.pos_of_ne_zero hN
  let u : (𝓞 F)ˣ := (hζi.isUnit hN).unit
  let ζo : (Localization.Away (n : 𝓞 F))ˣ := Units.map (algebraMap (𝓞 F) _).toMonoidHom u
  have hkunit : IsUnit ((n ^ e : ℕ) : Localization.Away (n : 𝓞 F)) := by
    have := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F))
      (n : 𝓞 F)).pow e
    simpa using this
  have hprim : ∀ (K : Type) [Field K] (β : Localization.Away (n : 𝓞 F) →+* K),
      IsPrimitiveRoot (β ζo) (n ^ e) := by
    intro K _ β
    have hroot := (hζi.isRoot_cyclotomic hpos).map (f := β.comp (algebraMap (𝓞 F) _))
    rw [Polynomial.map_cyclotomic] at hroot
    haveI : NeZero ((n ^ e : ℕ) : K) := ⟨by simpa using (hkunit.map β).ne_zero⟩
    exact Polynomial.isRoot_cyclotomic_iff.mp hroot
  let b : _root_.GlobalTheory.ZM.TBase (Localization.Away (n : 𝓞 F)) (n ^ e) := ⟨ζo, hkunit, hprim⟩
  have hcompx : ∀ a : 𝓞 F, em (algebraMap _ _ a) = ((a : F) : ℂ) := fun a =>
    RingHom.congr_fun hcomp a
  have hmemZ : ∀ x, em x ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : 𝓞 F)) x
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hspec := congrArg em (IsLocalization.mk'_spec (Localization.Away (n : 𝓞 F)) a s)
    rw [map_mul, hcompx, hcompx, ← hm] at hspec
    have hnm : (((((n : 𝓞 F) ^ m : 𝓞 F)) : F) : ℂ) = (n : ℂ) ^ m := by simp
    rw [hnm] at hspec
    have hn0 : (n : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne_zero)
    rw [eq_div_of_mul_eq hn0 hspec, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (_root_.GlobalTheory.ZM.CycBase.mem_ZP p n e hn a)
      (pow_mem (inv_natCast_mem_ZP_of_coprime hcop) m)
  refine ⟨Localization.Away (n : 𝓞 F), inferInstance, b, em, em.codRestrict _ hmemZ, har, ?_,
    fun x => rfl, ?_⟩
  · apply Subtype.ext
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP
    change em (algebraMap (𝓞 F) _ hζ.toInteger) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e)
    rw [hcompx]
    exact congrArg Subtype.val hζ.coe_toInteger
  · intro K _ y
    exact spec_dualNumber_hom_ZP_eq_constPt hcop hn.ne_zero y

end GlobalTheory.ZM.CycBase
end
