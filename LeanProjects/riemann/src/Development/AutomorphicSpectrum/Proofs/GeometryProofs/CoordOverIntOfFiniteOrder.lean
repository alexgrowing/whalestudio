import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordBase

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_of_inv_mem (S : Subring Ω) {w : Ω} (hw0 : w ≠ 0) (hinv : w⁻¹ ∈ S)
    (hi : IsIntegral ℤ w) : w ∈ S := by
  obtain ⟨P, hm, hP⟩ := hi
  have hdeg : P.natDegree ≠ 0 := by
    intro h0
    have c0 : P.coeff 0 = 1 := by
      have := hm.coeff_natDegree
      rwa [h0] at this
    have h1 : P = 1 := by
      have := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [c0] at this
      simpa using this
    simp [h1] at hP
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdeg
  have hlead : P.coeff (n + 1) = 1 := by
    have := hm.coeff_natDegree
    rwa [hn] at this
  rw [Polynomial.eval₂_eq_sum_range, hn, Finset.sum_range_succ, hlead] at hP
  have hterm : ∀ i ∈ Finset.range (n + 1), (algebraMap ℤ Ω) (P.coeff i) * w ^ i =
      ((algebraMap ℤ Ω) (P.coeff i) * (w⁻¹) ^ (n - i)) * w ^ n := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e : w ^ n = w ^ i * w ^ (n - i) := by rw [← pow_add]; congr 1; omega
    rw [e, inv_pow]
    have : w ^ (n - i) ≠ 0 := pow_ne_zero _ hw0
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, map_one, _root_.one_mul, pow_succ', ← add_mul] at hP
  have hz := (mul_eq_zero.1 hP).resolve_right (pow_ne_zero _ hw0)
  rw [eq_neg_of_add_eq_zero_right hz]
  refine S.neg_mem (S.sum_mem fun i _ => S.mul_mem ?_ (S.pow_mem hinv _))
  rw [eq_intCast]
  exact intCast_mem S _

def val (U : X.Opens) (hg : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (genPt ξ) hg).hom

theorem genMap_germ_val (U : X.Opens) (hg : genPt ξ ∈ U) (p : Cpt ξ) (hp : p.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = val U hg s :=
  RegAtRing.genMap_germ p U hp hg s

theorem exists_pow_mul_mem {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U)
    (hc : ∀ q ∈ U, genPt ξ ⤳ q) (f : Γ(X, U)) (a : Ω)
    (ha : ∀ (q : X) (hq : q ∈ U), IsUnit (X.presheaf.germ U q hq f) → a ∈ regAt ξ ⟨q, hc q hq⟩) :
    ∃ (n : ℕ) (b : Γ(X, U)), val U hg b = val U hg f ^ n * a := by
  let I : Ideal Γ(X, U) :=
    { carrier := {u | ∃ t, val U hg t = val U hg u * a}
      add_mem' := by
        rintro u v ⟨t, ht⟩ ⟨s, hs⟩
        exact ⟨t + s, by rw [map_add, map_add, ht, hs, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨t, ht⟩
        exact ⟨c * t, by rw [smul_eq_mul, map_mul, map_mul, ht, _root_.mul_assoc]⟩ }
  suffices hf : f ∈ I.radical by
    obtain ⟨n, t, ht⟩ := hf
    exact ⟨n, t, by rw [ht, map_pow]⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hIP, hP⟩
  by_contra hfP
  let q : U := ⟨hU.fromSpec ⟨P, hP⟩, hU.range_fromSpec.le ⟨⟨P, hP⟩, rfl⟩⟩
  have hq : hU.primeIdealOf q = ⟨P, hP⟩ :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf q
  have hloc := hU.isLocalization_stalk q
  rw [hq] at hloc
  have hunit : ∀ u, u ∉ P → IsUnit (X.presheaf.germ U q.1 q.2 u) := fun u hu =>
    IsLocalization.map_units (M := P.primeCompl) (X.presheaf.stalk q.1) ⟨u, hu⟩
  obtain ⟨s, hs⟩ := ha q.1 q.2 (hunit f hfP)
  obtain ⟨⟨t, u⟩, e⟩ := IsLocalization.surj P.primeCompl s
  have e' : s * X.presheaf.germ U q.1 q.2 u.1 = X.presheaf.germ U q.1 q.2 t := e
  refine u.2 (hIP ⟨t, ?_⟩)
  have h2 := congrArg (genMap ξ ⟨q.1, hc _ q.2⟩) e'
  rw [map_mul, hs, genMap_germ_val U hg ⟨q.1, hc _ q.2⟩ q.2, genMap_germ_val U hg ⟨q.1, hc _ q.2⟩ q.2] at h2
  rw [← h2, mul_comm]

theorem mem_regAt_gen (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, rfl⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  exact congrArg (fun φ => φ.hom s)
    ((congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e).trans (Category.id_comp _))

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem inChart_gen (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ :=
  ⟨hc, fun _ => mem_regAt_gen hT.gen _⟩

theorem mem_adjoin_iff (hT : CoordTie o ξ x) {c : κ} (hxc : x c ≠ 0) {U : X.Opens}
    (hU : IsAffineOpen U) (hmem : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (hg : genPt ξ ∈ U) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ b : Γ(X, U), val U hg b = a := by
  have hc : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => ((hmem q).1 hq).1
  constructor
  · intro ha
    have hreg := (hT.ring c hxc a).1 ha
    obtain ⟨n, b, hb⟩ := exists_pow_mul_mem hU hg hc 1 a
      (fun q hq _ => hreg _ ((hmem q).1 hq).2)
    exact ⟨b, by simpa using hb⟩
  · rintro ⟨b, rfl⟩
    refine (hT.ring c hxc _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨_, genMap_germ_val U hg p hpU b⟩

end Chart

section Main

variable {o : Type} [CommRing o] [Algebra o Ω] {κ M : Type} {x : κ → Ω} {w : M → Ω} {m₀ : M}

theorem mem_regAt_of_inChart (hT : CoordTie o ξ x) (hwo : ∀ m, w m ∈ (algebraMap o Ω).range) {c : κ}
    {p : Cpt ξ} (hp : InChart ξ x c p) (m : M) : w m ∈ regAt ξ p := by
  obtain ⟨r, hr⟩ := hwo m
  refine (hT.ring c hp.1 _).1 ?_ p hp
  rw [← hr]
  exact Subalgebra.algebraMap_mem _ r

theorem inChart_mul_iff (hT : CoordTie o ξ x) (hwo : ∀ m, w m ∈ (algebraMap o Ω).range)
    (h0 : w m₀ = 1) {c : κ} {m : M} (hxc : x c ≠ 0) (hwm : w m ≠ 0) {U : X.Opens}
    (hmem : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hg : genPt ξ ∈ U)
    {f : Γ(X, U)} (hf : val U hg f = w m) (p : Cpt ξ) :
    InChart ξ (fun j : κ × M => w j.2 * x j.1) (c, m) p ↔
      ∃ hp : p.1 ∈ U, IsUnit (X.presheaf.germ U p.1 hp f) := by
  constructor
  · rintro ⟨-, hr⟩
    have hx : InChart ξ x c p := ⟨hxc, fun c' => by
      have h1 : w m * x c' / (w m * x c) ∈ regAt ξ p := hr (c', m)
      rwa [mul_div_mul_left _ _ hwm] at h1⟩
    have hp : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hx⟩
    refine ⟨hp, ?_⟩
    obtain ⟨s, hs⟩ : (w m)⁻¹ ∈ regAt ξ p := by
      have h1 : w m₀ * x c / (w m * x c) ∈ regAt ξ p := hr (c, m₀)
      have e : w m₀ * x c / (w m * x c) = (w m)⁻¹ := by rw [h0]; field_simp
      rwa [e] at h1
    refine isUnit_iff_exists_inv.2 ⟨s, hT.gen.inj p ?_⟩
    rw [map_mul, map_one, hs, genMap_germ_val U hg p hp, hf, mul_inv_cancel₀ hwm]
  · rintro ⟨hp, hu⟩
    have hx : InChart ξ x c p := ((hmem p.1).1 hp).2
    refine ⟨mul_ne_zero hwm hxc, fun ⟨c', m'⟩ => ?_⟩
    have hinv : (w m)⁻¹ ∈ regAt ξ p := by
      have h1 := (RegAtMono.unitAt_of_isUnit ξ p hu).2.2
      rwa [genMap_germ_val U hg p hp, hf] at h1
    have e : w m' * x c' / (w m * x c) = w m' * (x c' / x c) * (w m)⁻¹ := by field_simp
    show w m' * x c' / (w m * x c) ∈ regAt ξ p
    rw [e]
    exact mul_mem (mul_mem (mem_regAt_of_inChart hT hwo hx m') (hx.2 c')) hinv

theorem coordTie_mul (hT : CoordTie o ξ x) (hwo : ∀ m, w m ∈ (algebraMap o Ω).range) (h0 : w m₀ = 1)
    (hint : ∀ m, IsIntegral ℤ (w m))
    (hgen : ∀ S : Subring Ω, (∀ m, w m ∈ S) → ∀ r : o, algebraMap o Ω r ∈ S) :
    CoordTie ℤ ξ (fun j : κ × M => w j.2 * x j.1) := by
  have data : ∀ (c : κ) (m : M), x c ≠ 0 → ∃ (U : X.Opens) (_ : IsAffineOpen U) (hg : genPt ξ ∈ U)
      (f : Γ(X, U)), (∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) ∧
        val U hg f = w m := by
    intro c m hxc
    obtain ⟨U, hU, hmem⟩ := hT.affine c hxc
    have hg : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, inChart_gen hT hxc⟩
    obtain ⟨r, hr⟩ := hwo m
    have hw : w m ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
      rw [← hr]
      exact Subalgebra.algebraMap_mem _ r
    obtain ⟨f, hf⟩ := (mem_adjoin_iff hT hxc hU hmem hg _).1 hw
    exact ⟨U, hU, hg, f, hmem, hf⟩
  refine ⟨hT.gen, fun p => ?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hT.cover p
    refine ⟨(c, m₀), ?_, fun ⟨c', m'⟩ => ?_⟩
    · show w m₀ * x c ≠ 0
      rw [h0, _root_.one_mul]
      exact hc.1
    · show w m' * x c' / (w m₀ * x c) ∈ regAt ξ p
      rw [h0, _root_.one_mul, mul_div_assoc]
      exact mul_mem (mem_regAt_of_inChart hT hwo hc m') (hc.2 c')
  · rintro ⟨c, m⟩ hy
    have hy' : w m * x c ≠ 0 := hy
    have hwm := left_ne_zero_of_mul hy'
    have hxc := right_ne_zero_of_mul hy'
    obtain ⟨U, hU, hg, f, hmem, hf⟩ := data c m hxc
    refine ⟨X.basicOpen f, hU.basicOpen f, fun q => ?_⟩
    constructor
    · intro hq
      have hqU := X.basicOpen_le f hq
      have hc : genPt ξ ⤳ q := ((hmem q).1 hqU).1
      exact ⟨hc, (inChart_mul_iff hT hwo h0 hxc hwm hmem hg hf ⟨q, hc⟩).2
        ⟨hqU, (X.mem_basicOpen f q hqU).1 hq⟩⟩
    · rintro ⟨hc, hq⟩
      obtain ⟨hqU, hu⟩ := (inChart_mul_iff hT hwo h0 hxc hwm hmem hg hf ⟨q, hc⟩).1 hq
      exact (X.mem_basicOpen f q hqU).2 hu
  · rintro ⟨c, m⟩ hy a
    have hy' : w m * x c ≠ 0 := hy
    have hwm := left_ne_zero_of_mul hy'
    have hxc := right_ne_zero_of_mul hy'
    obtain ⟨U, hU, hg, f, hmem, hf⟩ := data c m hxc
    constructor
    · intro ha p hp
      have hle : Algebra.adjoin ℤ (Set.range fun j : κ × M =>
          (w j.2 * x j.1) / (w m * x c)) ≤ subalgebraOfSubring (regAt ξ p) :=
        Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hp.2 j)
      exact hle ha
    · intro hreg
      let S : Subring Ω := (Algebra.adjoin ℤ (Set.range fun j : κ × M =>
          (w j.2 * x j.1) / (w m * x c))).toSubring
      have gen : ∀ j : κ × M, (w j.2 * x j.1) / (w m * x c) ∈ S :=
        fun j => Algebra.subset_adjoin ⟨j, rfl⟩
      have hinv : (w m)⁻¹ ∈ S := by
        have h1 := gen (c, m₀)
        have e : w m₀ * x c / (w m * x c) = (w m)⁻¹ := by rw [h0]; field_simp
        rwa [e] at h1
      have hwS : w m ∈ S := mem_of_inv_mem S hwm hinv (hint m)
      have hall : ∀ m', w m' ∈ S := fun m' => by
        have h1 := S.mul_mem (gen (c, m')) hwS
        have e : w m' * x c / (w m * x c) * w m = w m' := by field_simp
        rwa [e] at h1
      have hxS : ∀ c', x c' / x c ∈ S := fun c' => by
        have h1 := gen (c', m)
        have e : w m * x c' / (w m * x c) = x c' / x c := mul_div_mul_left _ _ hwm
        rwa [e] at h1
      let B : Subalgebra o Ω := { S.toSubsemiring with algebraMap_mem' := hgen S hall }
      have hle : Algebra.adjoin o (Set.range fun j => x j / x c) ≤ B :=
        Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact hxS j)
      have hc : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => ((hmem q).1 hq).1
      obtain ⟨n, b, hb⟩ := exists_pow_mul_mem hU hg hc f a fun q hq hu =>
        hreg _ ((inChart_mul_iff hT hwo h0 hxc hwm hmem hg hf ⟨q, hc q hq⟩).2 ⟨hq, hu⟩)
      have hbS : val U hg b ∈ S := hle ((mem_adjoin_iff hT hxc hU hmem hg _).2 ⟨b, rfl⟩)
      have e : a = val U hg b * ((w m)⁻¹) ^ n := by
        rw [hb, hf, inv_pow]
        have : w m ^ n ≠ 0 := pow_ne_zero _ hwm
        field_simp
      show a ∈ S
      rw [e]
      exact S.mul_mem hbS (S.pow_mem hinv n)

theorem coordTie_reindex {J J' : Type} (e : J' ≃ J) {y : J → Ω} (h : CoordTie ℤ ξ y) :
    CoordTie ℤ ξ (fun j => y (e j)) := by
  have hI : ∀ (c : J') (p : Cpt ξ), InChart ξ (fun j => y (e j)) c p ↔ InChart ξ y (e c) p :=
    fun c p => ⟨fun ⟨h0, h1⟩ => ⟨h0, fun j => by simpa using h1 (e.symm j)⟩,
      fun ⟨h0, h1⟩ => ⟨h0, fun j => h1 _⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hI _ _).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hm⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => (hm q).trans (exists_congr fun _ => (hI _ _).symm)⟩
  · have hr : (Set.range fun j => y (e j) / y (e c)) = Set.range fun j => y j / y (e c) :=
      e.surjective.range_comp (fun j => y j / y (e c))
    rw [hr, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hI _ _).symm Iff.rfl

end Main

end GlobalTheory.CompanionTheory.Ar.CoordBase

namespace GlobalTheory.CompanionTheory.Ar

theorem coordTie_int_of_finite : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (o : Type) [CommRing o] [Algebra o Ω] [Module.Finite ℤ o] (κ : Type) [Finite κ] (x : κ → Ω),
    CoordTie o ξ x → ∃ (N : ℕ) (x' : Fin (N + 1) → Ω), CoordTie ℤ ξ x' := by
  intro X Ω _ ξ o _ _ _ κ _ x hT
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := o)
  let w : Option (Fin n) → Ω := fun m => m.elim 1 (fun i => algebraMap o Ω (g i))
  have hwo : ∀ m, w m ∈ (algebraMap o Ω).range := by
    rintro (_ | i)
    · exact ⟨1, map_one _⟩
    · exact ⟨g i, rfl⟩
  have hint : ∀ m, IsIntegral ℤ (w m) := by
    intro m
    obtain ⟨r, hr⟩ := hwo m
    rw [← hr]
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) r).map (algebraMap o Ω).toIntAlgHom
  have hgen : ∀ S : Subring Ω, (∀ m, w m ∈ S) → ∀ r : o, algebraMap o Ω r ∈ S := by
    intro S hS r
    have hr : r ∈ Submodule.span ℤ (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun r _ => algebraMap o Ω r ∈ S) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      exact hS (some i)
    · rw [map_zero]
      exact S.zero_mem
    · intro a b _ _ ha hb
      rw [map_add]
      exact S.add_mem ha hb
    · intro k a _ ha
      have e : algebraMap o Ω (k • a) = k • algebraMap o Ω a := map_zsmul _ _ _
      rw [e]
      exact zsmul_mem ha k
  obtain ⟨c, -⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Nonempty (κ × Option (Fin n)) := ⟨(c, none)⟩
  have hcard : 0 < Nat.card (κ × Option (Fin n)) := Nat.card_pos
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  exact ⟨N, _, CoordBase.coordTie_reindex (Finite.equivFinOfCardEq hN).symm
    (CoordBase.coordTie_mul (m₀ := none) hT hwo rfl hint hgen)⟩

end GlobalTheory.CompanionTheory.Ar
