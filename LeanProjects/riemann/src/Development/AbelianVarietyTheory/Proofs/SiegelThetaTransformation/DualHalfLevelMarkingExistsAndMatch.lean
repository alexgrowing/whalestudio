import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DualMark

section Abstract

variable {R P A : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]

theorem exists_nsmul {B : LinearMap.BilinForm ℤ P} (hB : Function.Bijective B) {m : ℕ} (hm : m ≠ 0) {x : P}
    (h : ∀ y, (m : ℤ) ∣ B x y) : ∃ z, x = m • z := by
  let f : P →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / m
      map_add' := fun a b => by rw [map_add, Int.add_ediv_of_dvd_left (h a)]
      map_smul' := fun k a => by
        rw [map_zsmul]; simp only [smul_eq_mul, RingHom.id_apply]; exact Int.mul_ediv_assoc _ (h a) }
  obtain ⟨z, hz⟩ := hB.2 f
  refine ⟨z, hB.1 ?_⟩
  ext y
  rw [map_nsmul, hz]
  simp only [LinearMap.smul_apply, nsmul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Int.mul_ediv_cancel' (h y)).symm

theorem smul_eq_nsmul {I J : Ideal R} {m : ℕ} (h : J * I ≤ Ideal.span {(m : R)}) {a : R} (ha : a ∈ J) {x : P}
    (hx : x ∈ I • (⊤ : Submodule R P)) : ∃ z, a • x = m • z := by
  refine Submodule.smul_induction_on hx (fun b hb y _ => ?_) ?_
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (h (Ideal.mul_mem_mul ha hb))
    exact ⟨t • y, by rw [← mul_smul, ← ht, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro u v ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by rw [smul_add, smul_add, hz, hw]⟩

theorem nsmul_mem {I : Ideal R} {m : ℕ} (hm : (m : R) ∈ I) (z : P) : m • z ∈ I • (⊤ : Submodule R P) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul hm trivial

theorem map_mem {I : Ideal R} (f : A →ₗ[R] P) {a : A} (ha : a ∈ I • (⊤ : Submodule R A)) :
    f a ∈ I • (⊤ : Submodule R P) := by
  have := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem exists_adj {s : R → R} {B : LinearMap.BilinForm ℤ P} {C : LinearMap.BilinForm ℤ A}
    (hB : Function.Bijective B) (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y))
    (aC : ∀ (a : R) x y, C (a • x) y = C x (s a • y)) (f : P →ₗ[R] A) :
    ∃ g : A →ₗ[R] P, ∀ x v, B (g x) v = C x (f v) := by
  choose g hg using fun x => hB.2 ((C x).comp f.toAddMonoidHom.toIntLinearMap)
  have hg' : ∀ x v, B (g x) v = C x (f v) := fun x v => by rw [hg]; rfl
  refine ⟨⟨⟨g, fun x y => hB.1 (LinearMap.ext fun v => ?_)⟩, fun a x => hB.1 (LinearMap.ext fun v => ?_)⟩, hg'⟩
  · simp only [map_add, LinearMap.add_apply, hg']
  · simp only [RingHom.id_apply, aB, hg', aC, map_smul]

variable {s : R →+* R} {I J : Ideal R} {m : ℕ} {c : R} {B : LinearMap.BilinForm ℤ P} {C : LinearMap.BilinForm ℤ A}

theorem dvd_of_mem (hIJ : J * I ≤ Ideal.span {(m : R)}) (hs : ∀ a ∈ I, s a ∈ J)
    (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y)) {x y : P} (hx : x ∈ I • (⊤ : Submodule R P))
    (hy : y ∈ I • (⊤ : Submodule R P)) : (m : ℤ) ∣ B x y := by
  refine Submodule.smul_induction_on hx (fun b hb u _ => ?_) (fun u v hu hv => ?_)
  · obtain ⟨z, hz⟩ := smul_eq_nsmul hIJ (hs b hb) hy
    rw [aB, hz, map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · rw [map_add, LinearMap.add_apply]; exact dvd_add hu hv

theorem mem_of_dvd (hm : m ≠ 0) (hmI : (m : R) ∈ I) (hss : ∀ a, s (s a) = a) (hs' : ∀ a ∈ J, s a ∈ I)
    (hc : c ∈ I) (hc1 : c - 1 ∈ J) (hB : Function.Bijective B)
    (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y)) {x : P}
    (h : ∀ y ∈ I • (⊤ : Submodule R P), (m : ℤ) ∣ B x y) : x ∈ I • (⊤ : Submodule R P) := by
  obtain ⟨z, hz⟩ := exists_nsmul hB hm (x := s c • x) fun y => by
    rw [aB, hss]; exact h _ (Submodule.smul_mem_smul hc trivial)
  have : x = m • z - s (c - 1) • x := by rw [map_sub, map_one, sub_smul, one_smul, hz]; simp
  rw [this]
  exact sub_mem (nsmul_mem hmI z) (Submodule.smul_mem_smul (hs' _ hc1) trivial)

theorem exists_inv [Module.Projective R P] (hIJ : J * I ≤ Ideal.span {(m : R)}) (hmJ : (m : R) ∈ J)
    (hc : c ∈ I) (hc1 : c - 1 ∈ J) (mk : A →ₗ[R] P)
    (inj : ∀ a ∈ I • (⊤ : Submodule R A), (∃ u, mk a = m • u) → ∃ b, a = m • b)
    (surj : ∀ v ∈ I • (⊤ : Submodule R P), ∃ a ∈ I • (⊤ : Submodule R A), ∃ u, v = mk a + m • u) :
    ∃ f : P →ₗ[R] A, ∀ a ∈ I • (⊤ : Submodule R A), ∃ b, f (mk a) = a + m • b := by
  have hIJ' : I * J ≤ Ideal.span {(m : R)} := mul_comm I J ▸ hIJ
  let q := Submodule.mapQ (J • (⊤ : Submodule R A)) (J • (⊤ : Submodule R P)) mk fun a ha => map_mem mk ha
  have hi : ∀ a, mk a ∈ J • (⊤ : Submodule R P) → a ∈ J • (⊤ : Submodule R A) := fun a ha => by
    obtain ⟨b, hb⟩ := inj (c • a) (Submodule.smul_mem_smul hc trivial) (by
      rw [map_smul]; exact smul_eq_nsmul hIJ' hc ha)
    have : a = m • b - (c - 1) • a := by rw [sub_smul, one_smul, hb]; simp
    rw [this]
    exact sub_mem (nsmul_mem hmJ b) (Submodule.smul_mem_smul hc1 trivial)
  have hq : Function.Surjective (q ∘ₗ (J • (⊤ : Submodule R A)).mkQ) := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨a, -, u, hu⟩ := surj (c • v) (Submodule.smul_mem_smul hc trivial)
    refine ⟨a, (Submodule.Quotient.eq _).2 ?_⟩
    have : mk a - v = (c - 1) • v - m • u := by rw [sub_smul, one_smul, hu]; abel
    rw [this]
    exact sub_mem (Submodule.smul_mem_smul hc1 trivial) (nsmul_mem hmJ u)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ (J • (⊤ : Submodule R P)).mkQ hq
  refine ⟨f, fun a ha => ?_⟩
  have h1 : f (mk a) - a ∈ J • (⊤ : Submodule R A) := hi _ (by
    rw [map_sub]; exact (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hf (mk a)))
  obtain ⟨b, hb⟩ := smul_eq_nsmul hIJ' hc h1
  obtain ⟨b', hb'⟩ := smul_eq_nsmul hIJ hc1 (sub_mem (map_mem f (map_mem mk ha)) ha)
  refine ⟨b - b', ?_⟩
  rw [smul_sub, ← hb, ← hb', sub_smul, one_smul]
  abel

theorem exists_pow_le (J K : Ideal R) [IsNoetherianRing R] [Finite (R ⧸ K)] :
    ∃ (t : R) (j : ℕ), t - 1 ∈ J ∧ ∀ a ∈ J ^ j, t * a ∈ K := by
  haveI : IsArtinian R (R ⧸ K) := isArtinian_of_finite
  let f : ℕ →o (Submodule R (R ⧸ K))ᵒᵈ :=
    ⟨fun j => OrderDual.toDual (J ^ j • ⊤), fun i j h =>
      Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨j, hj⟩ := IsArtinian.monotone_stabilizes f
  have h1 : (J ^ j • ⊤ : Submodule R (R ⧸ K)) = J ^ (j + 1) • ⊤ := hj (j + 1) (Nat.le_succ j)
  obtain ⟨t, ht, h⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (J ^ j • ⊤ : Submodule R (R ⧸ K)) (IsNoetherian.noetherian _) (by
      rw [← Submodule.mul_smul, ← pow_succ', ← h1])
  refine ⟨t, j, ht, fun a ha => ?_⟩
  have := h (a • 1) (Submodule.smul_mem_smul ha trivial)
  rwa [← mul_smul, Algebra.smul_def, _root_.mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at this

theorem exists_dual [Module.Projective R P] (hIJ : J * I ≤ Ideal.span {(m : R)}) (hmJ : (m : R) ∈ J)
    (hc : c ∈ I) (hc1 : c - 1 ∈ J) (hB : Function.Bijective B)
    (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y)) (aC : ∀ (a : R) x y, C (a • x) y = C x (s a • y))
    (mk : A →ₗ[R] P) (inj : ∀ a ∈ I • (⊤ : Submodule R A), (∃ u, mk a = m • u) → ∃ b, a = m • b)
    (surj : ∀ v ∈ I • (⊤ : Submodule R P), ∃ a ∈ I • (⊤ : Submodule R A), ∃ u, v = mk a + m • u) (k : ℤ) :
    ∃ δ : A →ₗ[R] P, ∀ x, ∀ a ∈ I • (⊤ : Submodule R A), (m : ℤ) ∣ k * C x a + B (δ x) (mk a) := by
  obtain ⟨f, hf⟩ := exists_inv hIJ hmJ hc hc1 mk inj surj
  obtain ⟨g, hg⟩ := exists_adj hB aB aC f
  refine ⟨(-k) • g, fun x a ha => ?_⟩
  obtain ⟨b, hb⟩ := hf a ha
  rw [LinearMap.smul_apply, map_zsmul, LinearMap.smul_apply, hg, hb, map_add, map_nsmul]
  exact ⟨-k * C x b, by simp only [smul_eq_mul, nsmul_eq_mul]; ring⟩

theorem mem_of_dual_mem (hIJ : J * I ≤ Ideal.span {(m : R)}) (hm : m ≠ 0) (hmI : (m : R) ∈ I)
    (hss : ∀ a, s (s a) = a) (hs : ∀ a ∈ I, s a ∈ J) (hs' : ∀ a ∈ J, s a ∈ I) (hc : c ∈ I) (hc1 : c - 1 ∈ J)
    (hC : Function.Bijective C) (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y))
    (aC : ∀ (a : R) x y, C (a • x) y = C x (s a • y)) {mk δ : A →ₗ[R] P} {k : ℤ} (hk : IsCoprime (m : ℤ) k)
    (h : ∀ x, ∀ a ∈ I • (⊤ : Submodule R A), (m : ℤ) ∣ k * C x a + B (δ x) (mk a)) {x : A}
    (hx : δ x ∈ I • (⊤ : Submodule R P)) : x ∈ I • (⊤ : Submodule R A) :=
  mem_of_dvd hm hmI hss hs' hc hc1 hC aC fun a ha => hk.dvd_of_dvd_mul_left
    ((dvd_add_left (dvd_of_mem hIJ hs aB hx (map_mem mk ha))).1 (h x a ha))

theorem exists_dual_sub_mem (hm : m ≠ 0) (hmI : (m : R) ∈ I)
    (hss : ∀ a, s (s a) = a) (hs' : ∀ a ∈ J, s a ∈ I) (hc : c ∈ I) (hc1 : c - 1 ∈ J)
    (hB : Function.Bijective B) (hC : Function.Bijective C) (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y))
    (aC : ∀ (a : R) x y, C (a • x) y = C x (s a • y)) {mk δ : A →ₗ[R] P} {k : ℤ} (hk : IsCoprime (m : ℤ) k)
    (surj : ∀ v ∈ I • (⊤ : Submodule R P), ∃ a ∈ I • (⊤ : Submodule R A), ∃ u, v = mk a + m • u)
    (h : ∀ x, ∀ a ∈ I • (⊤ : Submodule R A), (m : ℤ) ∣ k * C x a + B (δ x) (mk a)) (v : P) :
    ∃ x, v - δ x ∈ I • (⊤ : Submodule R P) := by
  obtain ⟨g, hg⟩ := exists_adj hC aC aB mk
  obtain ⟨p, q, hpq⟩ := hk
  refine ⟨(-q) • g v, mem_of_dvd hm hmI hss hs' hc hc1 hB aB fun y hy => ?_⟩
  obtain ⟨a, ha, u, rfl⟩ := surj y hy
  obtain ⟨t, ht⟩ := h ((-q) • g v) a ha
  rw [map_zsmul, LinearMap.smul_apply, hg, smul_eq_mul] at ht
  rw [map_add, map_nsmul, nsmul_eq_mul]
  refine dvd_add ⟨p * B v (mk a) - t, ?_⟩ (Dvd.intro _ rfl)
  rw [map_sub, LinearMap.sub_apply]
  linear_combination (-1 : ℤ) * ht - B v (mk a) * hpq

theorem mark_eq_of_dual (hIJ : J * I ≤ Ideal.span {(m : R)}) (hm : m ≠ 0) (hs : ∀ a ∈ I, s a ∈ J)
    (hB : Function.Bijective B) (aB : ∀ (a : R) x y, B (a • x) y = B x (s a • y))
    (sB : ∀ x y, B y x = -B x y) {mk δ mk' δ' : A →ₗ[R] P} {k : ℤ}
    (h : ∀ x, ∀ a ∈ I • (⊤ : Submodule R A), (m : ℤ) ∣ k * C x a + B (δ x) (mk a))
    (h' : ∀ x, ∀ a ∈ I • (⊤ : Submodule R A), (m : ℤ) ∣ k * C x a + B (δ' x) (mk' a))
    (hs : ∀ v, ∃ x, v - δ x ∈ I • (⊤ : Submodule R P)) (hd : ∀ x, δ x - δ' x ∈ I • (⊤ : Submodule R P))
    {a : A} (ha : a ∈ I • (⊤ : Submodule R A)) : ∃ u, mk a - mk' a = m • u := by
  refine exists_nsmul hB hm fun y => ?_
  obtain ⟨x, hx⟩ := hs y
  have h1 := dvd_of_mem hIJ ‹_› aB hx (sub_mem (map_mem mk ha) (map_mem mk' ha))
  have h2 := dvd_of_mem hIJ ‹_› aB (hd x) (map_mem mk' ha)
  have h3 := dvd_sub (dvd_add h1 (dvd_sub (h x a ha) (h' x a ha))) h2
  rw [sB, dvd_neg]
  convert h3 using 1
  simp only [map_sub, LinearMap.sub_apply]
  ring

end Abstract

theorem zpow_eq_iff {m k : ℕ} (hm : m ≠ 0) (a b : ℤ) :
    cexp (2 * Real.pi * I * (k / m)) ^ a = cexp (-(2 * Real.pi * I * (((m : ℚ)⁻¹ * b : ℚ) : ℂ))) ↔
      (m : ℤ) ∣ k * a + b := by
  have hp := Complex.isPrimitiveRoot_exp m hm
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [← hp.zpow_eq_one_iff_dvd, ← Complex.exp_int_mul, ← Complex.exp_int_mul, Complex.exp_neg,
    ← mul_eq_one_iff_eq_inv₀ (Complex.exp_ne_zero _), ← Complex.exp_add]
  congr! 2
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {X : Data E r} {L : Lt E r}

theorem exists_form (H : Host E) (hL : SelfD X L) : ∃ B : LinearMap.BilinForm ℤ L, Function.Bijective B ∧
    (∀ (a : 𝓞 E) x y, B (a • x) y = B x (H.bar a • y)) ∧ (∀ x y, B y x = -B x y) ∧
    ∀ x y : L, EF X x y = B x y := by
  have h0 : X.κ0 / 2 ≠ 0 := by
    have := X.ξ0_ne
    rcases X.κ0_xi with k | k <;> simp [k, this]
  have hlat : ReciprocityTheory.MultiplicativeHeights.IsLattice L := ⟨hL.1, TensLat.span_of_selfD X hL⟩
  have hp := (perfect_iff_traceFormDual_eq h0 X.Gm_det hlat).2 (by ext x; exact (hL.2 x).symm)
  have hB : ∀ x y : L, EF X x y = latticeEF _ _ L hp.1 x y := fun x y => (latticeEF_apply hp.1 x y).symm
  refine ⟨latticeEF _ _ L hp.1, (latticeEF_bijective_iff hp.1 hlat h0).2 ⟨X.Gm_det, hp.2⟩,
    fun a x y => ?_, fun x y => ?_, hB⟩
  · apply Int.cast_injective (α := ℚ)
    rw [← hB, ← hB, Submodule.coe_smul, Submodule.coe_smul, ← algebraMap_smul E a, ← algebraMap_smul E (H.bar a),
      TensLat.EF_smul]
    congr 2
    exact (H.bar_eq a).symm
  · apply Int.cast_injective (α := ℚ)
    rw [Int.cast_neg, ← hB, ← hB, TensLat.EF_swap]

theorem ef_inv_smul (m : ℕ) (u v : Fin r → E) : EF X u ((m : E)⁻¹ • v) = (m : ℚ)⁻¹ * EF X u v := by
  have : (m : E)⁻¹ • v = (m : ℚ)⁻¹ • v := by rw [← Rat.cast_smul_eq_qsmul E]; simp
  rw [this, TensLat.EF_eq_bilin, TensLat.EF_eq_bilin, map_smul, smul_eq_mul]

theorem prod_le (l : Geo.Tor.Level H) : l.Mb * Mfr l ≤ Ideal.span {(l.M : 𝓞 E)} := l.prod.le

theorem level_ne (l : Geo.Tor.Level H) : l.M ≠ 0 := by have := l.three_le; omega

theorem isDual_iff {B : LinearMap.BilinForm ℤ L} (hB : ∀ x y : L, EF X x y = B x y) (k : ℕ)
    (mk δ : Dw.La →ₗ[𝓞 E] L) :
    IsDual X l (cexp (2 * Real.pi * I * (k / l.M))) L (L.subtype ∘ₗ mk) (L.subtype ∘ₗ δ) ↔
      ∀ x, ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), (l.M : ℤ) ∣ (k : ℤ) * Dw.EF x a + B (δ x) (mk a) := by
  have key : ∀ x, ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La),
      (cexp (2 * Real.pi * I * (k / l.M)) ^ Dw.EF x (cSep l • a) =
        cexp (-(2 * Real.pi * I * ((EF X (δ x) (((l.M : E)⁻¹) • (mk a : Fin r → E)) : ℚ) : ℂ))) ↔
      (l.M : ℤ) ∣ (k : ℤ) * Dw.EF x a + B (δ x) (mk a)) := by
    intro x a ha
    obtain ⟨z, hz⟩ := smul_eq_nsmul (prod_le l) (LevelPairing.cSep_spec l).2 ha
    rw [sub_smul, one_smul, sub_eq_iff_eq_add] at hz
    rw [ef_inv_smul, hB, zpow_eq_iff (level_ne l), hz, map_add, map_nsmul, nsmul_eq_mul, mul_add, add_assoc]
    exact dvd_add_right (Dvd.dvd.mul_left (Dvd.intro _ rfl) _)
  exact ⟨fun h x a ha => (key x a ha).1 (h.pair x a ha),
    fun h => ⟨fun a => (δ a).2, fun x a ha => (key x a ha).2 (h x a ha)⟩⟩

theorem conj_half (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun a ha => Ideal.subset_span
    ⟨H.bar a, Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha, ?_⟩
  · rintro a ⟨b, hb, h⟩
    have : a = H.bar b := Subtype.ext (h.trans (H.bar_eq b).symm)
    rw [this]
    exact LevelPairing.bar_mem_Mb hb
  · conv_lhs => rw [← LevelPairing.bar_bar H a]
    exact H.bar_eq _

theorem exists_roots (l : Geo.Tor.Level H) (mk : Dw.La →ₗ[𝓞 E] L) (n N : ℕ) (hN : 0 < N) :
    ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L (L.subtype ∘ₗ mk) N Y := by
  have hK : Ideal.span {((2 * N : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hK
  obtain ⟨t, j, ht, hj⟩ := exists_pow_le l.Mb (Ideal.span {((2 * N : ℕ) : 𝓞 E)})
  have hM : (l.M : E) ≠ 0 := by exact_mod_cast level_ne l
  have hc := LevelPairing.cSep_spec l
  have hmem : ∀ q : LevQ Dw l, cSep l • levRep q ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := fun q =>
    Submodule.smul_mem_smul hc.1 trivial
  have key : ∀ a ∈ l.Mb, ∀ q : LevQ Dw l, ∃ z : L,
      a • ((l.M : E)⁻¹ • (mk (cSep l • levRep q) : Fin r → E)) = z := fun a ha q => by
    obtain ⟨z, hz⟩ := smul_eq_nsmul (prod_le l) ha (map_mem mk (hmem q))
    refine ⟨z, ?_⟩
    rw [smul_comm, ← Submodule.coe_smul, hz, AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul E,
      inv_smul_smul₀ hM]
  refine ⟨fun q => Matrix.of fun b => t • ((l.M : E)⁻¹ • (mk (cSep l • levRep (q b)) : Fin r → E)),
    fun q b => ⟨⟨_, hmem (q b), ?_, ?_⟩, j + 1, fun a ha => ?_⟩⟩
  · have h : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l) = q b :=
      Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
    refine Eq.trans ((Submodule.Quotient.eq _).2 ?_) h
    have := Submodule.smul_mem_smul hc.2 (Submodule.mem_top (x := levRep (q b)))
    rwa [sub_smul, one_smul] at this
  · obtain ⟨z, hz⟩ := key _ ht (q b)
    rw [sub_smul, one_smul] at hz
    exact hz ▸ z.2
  · change ∃ u ∈ L, a • t • ((l.M : E)⁻¹ • (mk (cSep l • levRep (q b)) : Fin r → E)) = _
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) ?_
    · obtain ⟨z, hz⟩ := key y hy (q b)
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hj x hx)
      refine ⟨w • z, L.smul_mem w z.2, ?_⟩
      rw [← mul_smul, mul_right_comm, mul_smul, hz, mul_comm x t, ← hw, mul_comm w, mul_smul,
        Nat.cast_smul_eq_nsmul]
    · rintro x y ⟨u, hu, h⟩ ⟨v, hv, h'⟩
      exact ⟨u + v, add_mem hu hv, by rw [add_smul, h, h', smul_add]⟩

theorem isMark_map {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : IsMark l L mk) (ga : GL (Fin r) E) :
    IsMark l (mapL ga L) (mvMap ga mk) := by
  let T := (Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)
  have hT : Function.Injective T := Matrix.mulVec_injective_iff_isUnit.2 ga.isUnit
  refine ⟨fun a => Submodule.mem_map_of_mem (h.mem a), fun a ha hu => h.inj a ha ?_, fun v hv => ?_⟩
  · obtain ⟨_, ⟨u, hu, rfl⟩, h1⟩ := hu
    exact ⟨u, hu, hT (by rw [map_nsmul]; exact h1)⟩
  · rw [mapL, ← Submodule.map_smul''] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    obtain ⟨a, ha, u, hu, rfl⟩ := h.surj v hv
    exact ⟨a, ha, T u, Submodule.mem_map_of_mem hu, by rw [map_add, map_nsmul]; rfl⟩

theorem isDual_map {ζ : ℂ} {mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : IsDual X l ζ L mk δ) {ga : GL (Fin r) E}
    (hg : IsUn X ga) : IsDual X l ζ (mapL ga L) (mvMap ga mk) (mvMap ga δ) := by
  refine ⟨fun a => Submodule.mem_map_of_mem (h.mem a), fun x a ha => ?_⟩
  rw [h.pair x a ha, EF_def, EF_def, ← hg, Matrix.mulVec_smul]
  rfl

theorem exists_eq_comp {f : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : ∀ a, f a ∈ L) :
    ∃ g : Dw.La →ₗ[𝓞 E] L, f = L.subtype ∘ₗ g := ⟨f.codRestrict L h, rfl⟩

theorem dual_marking : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ζ : ℂ), SelfD X L → IsMark l L mk → IsPrimitiveRoot ζ l.M → (∃ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ) ∧ (∀ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ → L ≤ LinearMap.range δ ⊔ Mfr l • L ∧ (∀ a, δ a ∈ Mfr l • L ↔ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ ga : GL (Fin r) E, IsUn X ga → IsMark l (mapL ga L) (mvMap ga mk) ∧ IsDual X l ζ (mapL ga L) (mvMap ga mk) (mvMap ga δ)) ∧ ∀ mk' δ' : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk' → IsDual X l ζ L mk' δ' → (∀ a, δ a - δ' a ∈ Mfr l • L) → ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) ∧ conjI (Mfr l) = l.Mb ∧ Mfr l * l.Mb = Ideal.span {(l.M : 𝓞 E)} ∧ ∀ n N : ℕ, 0 < N → ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y := by
  intro E _ _ _ H Dw l r X L mk ζ hL hmk hζ
  have hm := level_ne l
  obtain ⟨k, -, hk, rfl⟩ := (Complex.isPrimitiveRoot_iff ζ l.M hm).1 hζ
  have hk' : IsCoprime (l.M : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.2 hk.symm
  obtain ⟨B, hB, aB, sB, hE⟩ := exists_form H hL
  obtain ⟨mk, rfl⟩ := exists_eq_comp hmk.mem
  obtain ⟨hc, hc1⟩ := LevelPairing.cSep_spec l
  have hIJ := prod_le l
  have hMM : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := l.prod.ge (Ideal.subset_span rfl)
  have hmI : (l.M : 𝓞 E) ∈ Mfr l := Ideal.mul_le_right hMM
  have hmJ : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left hMM
  let s : 𝓞 E →+* 𝓞 E := H.bar
  have hss : ∀ a, s (s a) = a := LevelPairing.bar_bar H
  have hs : ∀ a ∈ Mfr l, s a ∈ l.Mb := fun a => LevelPairing.bar_mem_Mb
  have hs' : ∀ a ∈ l.Mb, s a ∈ Mfr l := fun a => Ideal.mem_map_of_mem s
  have aB' : ∀ (a : 𝓞 E) x y, B (a • x) y = B x (s a • y) := aB
  have aC : ∀ (a : 𝓞 E) x y, Dw.EF (a • x) y = Dw.EF x (s a • y) := Dw.adj
  have inj : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), (∃ u, mk a = l.M • u) → ∃ b, a = l.M • b := by
    rintro a ha ⟨u, hu⟩
    exact hmk.inj a ha ⟨u, u.2, congrArg Subtype.val hu⟩
  have surj : ∀ v ∈ Mfr l • (⊤ : Submodule (𝓞 E) L),
      ∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u, v = mk a + l.M • u := by
    intro v hv
    obtain ⟨a, ha, u, hu, h⟩ := hmk.surj v ((Submodule.mem_smul_top_iff _ _ _).1 hv)
    exact ⟨a, ha, ⟨u, hu⟩, Subtype.ext h⟩
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  refine ⟨?_, fun δ hδ => ?_, conj_half l, by rw [mul_comm]; exact l.prod, exists_roots l mk⟩
  · obtain ⟨δ, hδ⟩ := exists_dual hIJ hmJ hc hc1 hB aB' aC mk inj surj k
    exact ⟨_, (isDual_iff hE k mk δ).2 hδ⟩
  obtain ⟨δ, rfl⟩ := exists_eq_comp hδ.mem
  have h := (isDual_iff hE k mk δ).1 hδ
  have hsu := exists_dual_sub_mem hm hmI hss hs' hc hc1 hB Dw.unimod aB' aC hk' surj h
  refine ⟨fun v hv => ?_, fun a => ?_, fun ga hg => ⟨isMark_map hmk ga, isDual_map hδ hg⟩,
    fun mk' δ' hmk' hδ' hd a ha => ?_⟩
  · obtain ⟨x, hx⟩ := hsu ⟨v, hv⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, (Submodule.mem_smul_top_iff _ _ _).1 hx, add_sub_cancel _ _⟩
  · refine (Submodule.mem_smul_top_iff (Mfr l) L (δ a)).symm.trans ⟨fun hx => ?_, map_mem δ⟩
    exact mem_of_dual_mem hIJ hm hmI hss hs hs' hc hc1 Dw.unimod aB' aC hk' h hx
  · obtain ⟨mk', rfl⟩ := exists_eq_comp hmk'.mem
    obtain ⟨δ', rfl⟩ := exists_eq_comp hδ'.mem
    obtain ⟨u, hu⟩ := mark_eq_of_dual hIJ hm hs hB aB' sB h ((isDual_iff hE k mk' δ').1 hδ') hsu
      (fun x => (Submodule.mem_smul_top_iff _ _ _).2 (hd x)) ha
    exact ⟨u, u.2, congrArg Subtype.val (sub_eq_iff_eq_add'.1 hu)⟩

end GlobalTheory.Dict.DualMark
