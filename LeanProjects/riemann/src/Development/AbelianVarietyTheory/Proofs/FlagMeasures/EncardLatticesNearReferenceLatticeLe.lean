import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.NearCount

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩
    simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)

theorem smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)

theorem exists_gens [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)

end GlobalTheory.DegCnt.NearCount

theorem GlobalTheory.DegCnt.NearCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N m hm
  have hn : m * m ≠ ⊥ := mul_ne_zero hm hm
  obtain ⟨v, hv, hP⟩ := GlobalTheory.DegCnt.NearCount.exists_gens N (m * m) hn
  have h1 := GlobalTheory.DegCnt.NearCount.count_between N.P0 (m * m) hn _ v hv hP
  have h2 : ({P : Submodule (𝓞 K) V | m • N.P0 ≤ P ∧ m • P ≤ N.P0}).encard ≤
      {L : Submodule (𝓞 K) V | (m * m) • N.P0 ≤ L ∧ L ≤ N.P0}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun P => m • P) ?_
      (GlobalTheory.DegCnt.NearCount.smul_injective m hm).injOn
    rintro P ⟨h, h'⟩
    exact ⟨by rw [Submodule.mul_smul]; exact Submodule.smul_mono le_rfl h, h'⟩
  refine (ENat.toENNReal_le.2 (h2.trans h1)).trans (le_of_eq ?_)
  rw [map_mul, ← sq, ← pow_mul, ← sq]
  simp
