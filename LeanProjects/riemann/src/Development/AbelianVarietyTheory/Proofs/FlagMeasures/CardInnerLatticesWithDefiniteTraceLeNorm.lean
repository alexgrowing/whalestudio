import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.GlueZ

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_mem {t : K} (h : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 h
  have h1 : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    map_isIntegral_int (starRingEnd K) a.isIntegral_coe
  exact Submodule.mem_one.2 ⟨⟨_, h1⟩, rfl⟩

def Good (H : HermSpace K V) (S : Submodule K V) (z : V) (M : Submodule (𝓞 K) V) : Prop :=
  dual H M = M ∧ Submodule.span K (M : Set V) = S ∧ ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K)

variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem Good.z_mem (h : Good H S z M) : z ∈ M := by
  simpa using (h.2.2 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)

theorem Good.int (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy

theorem Good.mem_S (h : Good H S z M) {x : V} (hx : x ∈ M) : x ∈ S :=
  h.2.1 ▸ Submodule.subset_span hx

theorem Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩

theorem Good.exists_one (h : Good H S z M) (hz : H.B z z ≠ 0) : ∃ y ∈ M, H.B y z = 1 := by
  let J : Ideal (𝓞 K) :=
    (M.map ((H.B.flip z).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ a : 𝓞 K, a ∈ J ↔ ∃ y ∈ M, H.B y z = algebraMap (𝓞 K) K a := fun a => by
    simp [J]
  have hne : J ≠ ⊥ := by
    intro h0
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int h.z_mem h.z_mem)
    have : a ∈ J := (hJ a).2 ⟨z, h.z_mem, ha.symm⟩
    rw [h0, Ideal.mem_bot] at this
    exact hz (by rw [← ha, this, map_zero])
  have htop : J = ⊤ := by
    by_contra hJ1
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hne hJ1
    apply hx1
    rw [FractionalIdeal.mem_inv_iff (by simpa using hne)] at hx
    have h2 : star x • z ∈ M := by
      refine h.mem_of (S.smul_mem _ (h.mem_S h.z_mem)) fun y hy => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hy h.z_mem)
      have h3 := hx (algebraMap (𝓞 K) K a)
        (FractionalIdeal.mem_coeIdeal_of_mem _ ((hJ a).2 ⟨y, hy, ha.symm⟩))
      have h4 : x * algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K) := by
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h3
        exact Submodule.mem_one.2 ⟨b, hb⟩
      have h5 := star_mem h4
      rw [ha, star_mul', H.herm] at h5
      simpa using h5
    have h6 := star_mem ((h.2.2 _).1 h2)
    rw [star_star] at h6
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h6
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨y, hy, e⟩ := (hJ 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨y, hy, by rw [e, map_one]⟩

theorem Good.proj (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp

theorem count (T : ℕ) (hT : T ≠ 0) (hz : H.B z z = -(T : K)) (M₁ : Submodule (𝓞 K) V) (h₁ : Good H S z M₁) :
    {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)}.encard ≤
      (T ^ Module.finrank ℚ K : ℕ) := by
  have hz0 : H.B z z ≠ 0 := by rw [hz]; simpa using hT
  obtain ⟨y₁, hy₁, e₁⟩ := h₁.exists_one hz0
  have e₁' : H.B z y₁ = 1 := by rw [← H.herm, e₁, star_one]
  set 𝓢 := {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)} with h𝓢
  have key : ∀ M : Submodule (𝓞 K) V, ∃ (y : V) (u : K) (a : 𝓞 K), M ∈ 𝓢 →
      y ∈ M ∧ H.B y z = 1 ∧ y + u • z ∈ M₁ ∧ algebraMap (𝓞 K) K a = 1 - u * T := by
    intro M
    by_cases hM : M ∈ 𝓢
    swap
    · exact ⟨0, 0, 0, fun h => absurd h hM⟩
    obtain ⟨y, hy, e⟩ := hM.1.exists_one hz0
    have hm : y + (-H.B y y₁) • z ∈ M₁ := by
      refine h₁.mem_of (S.add_mem (hM.1.mem_S hy) (S.smul_mem _ (h₁.mem_S h₁.z_mem))) fun m hm => ?_
      obtain ⟨a, ha, ha0⟩ := h₁.proj hy₁ e₁ hm
      have h2 := hM.1.int hy ((hM.2 _ ha0).2 ha)
      have h3 : H.B z (m - a • y₁) = 0 := by rw [← H.herm, ha0, star_zero]
      have h4 : m = (m - a • y₁) + (algebraMap (𝓞 K) K a) • y₁ := by rw [algebraMap_smul]; abel
      generalize m - a • y₁ = m₀ at h2 h3 h4
      rw [h4]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3, e₁',
        smul_eq_mul]
      convert h2 using 1
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h₁.int hm h₁.z_mem)
    refine ⟨y, -H.B y y₁, a, fun _ => ⟨hy, e, hm, ?_⟩⟩
    rw [ha, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, e, hz, smul_eq_mul]
    ring
  choose y u a hyu using key
  let I : Ideal (𝓞 K) := Ideal.span {(T : 𝓞 K)}
  have hle : ∀ M ∈ 𝓢, ∀ M' ∈ 𝓢, Ideal.Quotient.mk I (a M) = Ideal.Quotient.mk I (a M') → M ≤ M' := by
    intro M hM M' hM' e
    obtain ⟨p1, p2, p3, p4⟩ := hyu M hM
    obtain ⟨q1, q2, q3, q4⟩ := hyu M' hM'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
    have hb' : algebraMap (𝓞 K) K b = u M' - u M := by
      have := congrArg (algebraMap (𝓞 K) K) hb
      rw [map_sub, map_mul, map_natCast, p4, q4] at this
      have hT' : (T : K) ≠ 0 := by exact_mod_cast hT
      apply mul_right_cancel₀ hT'
      rw [this]; ring
    have h5 : y M - y M' ∈ M₁ := by
      have := M₁.add_mem (M₁.sub_mem p3 q3) (M₁.smul_mem b h₁.z_mem)
      rw [← algebraMap_smul K b z, hb', sub_smul] at this
      convert this using 1
      abel
    have h6 : H.B (y M - y M') z = 0 := by rw [map_sub, LinearMap.sub_apply, p2, q2, sub_self]
    have h7 : y M ∈ M' := by simpa using M'.add_mem ((hM'.2 _ h6).2 h5) q1
    intro m hm
    obtain ⟨c, hc, hc0⟩ := hM.1.proj p1 p2 hm
    simpa using M'.add_mem ((hM'.2 _ hc0).2 ((hM.2 _ hc0).1 hc)) (M'.smul_mem c h7)
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h8 : 𝓢.encard ≤ (Set.univ : Set (𝓞 K ⧸ I)).encard :=
    Set.encard_le_encard_of_injOn (f := fun M => Ideal.Quotient.mk I (a M)) (fun _ _ => Set.mem_univ _)
      fun M hM M' hM' e => le_antisymm (hle M hM M' hM' e) (hle M' hM' M hM e.symm)
  refine h8.trans (le_of_eq ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem mem_lattice_zeroTorus {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]

end GlobalTheory.DegCnt.GlueZ

theorem GlobalTheory.DegCnt.GlueZ.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  have good : ∀ Λ', N.IsTerm g Λ' → GlueZ.Good H (uPerp N.F N.F') N.F'.z (latL N.F' N.F Λ') := fun Λ' h => by
    obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ' hg h
    exact ⟨h2.2, h2.1.2, h4⟩
  have hT : N.T ≠ 0 := by
    intro h0
    apply N.F'.hT
    rw [N.hT', h0, Nat.cast_zero]
  have hz : H.B N.F'.z N.F'.z = -(N.T : K) := N.hT' ▸ N.F'.zz
  have h1 := GlueZ.count N.T hT hz _ (good Λ hΛ)
  have h2 : {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧
      flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}.encard ≤ (N.T ^ Module.finrank ℚ K : ℕ) := by
    refine (Set.encard_le_encard ?_).trans h1
    rintro _ ⟨Λ', h, rfl, e⟩
    exact ⟨good Λ' h, fun y hy => by rw [GlueZ.mem_lattice_zeroTorus N Λ' y hy, GlueZ.mem_lattice_zeroTorus N Λ y hy, e]⟩
  haveI := hK.1
  have h3 : Module.finrank ℚ K = Formalism.HermitianLatticesTheory.fDeg K * 2 := by
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  refine (ENat.toENNReal_le.2 h2).trans (le_of_eq ?_)
  rw [NF.NT, ← pow_mul, ← h3, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rfl
