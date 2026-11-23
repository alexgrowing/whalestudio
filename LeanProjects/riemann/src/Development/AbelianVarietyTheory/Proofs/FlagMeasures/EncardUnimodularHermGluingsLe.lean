import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Glue

open TensorProduct

theorem finrank_baseChange_field (R M F : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] [Field F] [Algebra R F] :
    Module.finrank F (F ⊗[R] M) = Module.finrank R M := by
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := F) ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

theorem exists_gens (R M : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ t : Fin (Module.finrank R M) → M, ∀ N : Submodule R M, (∀ i, t i ∈ N) → I • (⊤ : Submodule R M) ≤ N →
      N = ⊤ := by
  have : Finite (MaximalSpectrum (R ⧸ I)) := inferInstance
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] M) (Module.finrank R M) (by
    intro P
    have := P.isMaximal
    let _ := Ideal.Quotient.field P.asIdeal
    rw [(AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) M).finrank_eq]
    exact finrank_baseChange_field R M _)
  have hs : Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) :=
    TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective
  choose t ht using fun i => hs (b i)
  refine ⟨t, fun N hN hI => eq_top_iff.2 fun m _ => ?_⟩
  choose a ha using fun i => Ideal.Quotient.mk_surjective (b.repr (TensorProduct.mk R (R ⧸ I) M 1 m) i)
  have h0 : TensorProduct.mk R (R ⧸ I) M 1 (m - ∑ i, a i • t i) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (TensorProduct.mk R (R ⧸ I) M 1 m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ht, ← ha, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have h1 : m - ∑ i, a i • t i ∈ I • (⊤ : Submodule R M) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← this]
    simp
  have h2 := N.add_mem (hI h1) (N.sum_mem (t := Finset.univ) fun i _ => N.smul_mem (a i) (hN i))
  simpa using h2

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem finrank_le {D : Submodule (𝓞 K) V} {W : Submodule K V} (h : D ≤ rs (𝓞 K) W) :
    Module.finrank (𝓞 K) D ≤ Module.finrank K W := by
  let f : D →ₗ[𝓞 K] W := { toFun := fun d => ⟨d, h d.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b e => Subtype.ext (congrArg (fun z : W => (z : V)) e)
  have h1 := LinearMap.rank_le_of_injective f hf
  rw [← IsLocalization.rank_eq (N := W) K (nonZeroDivisors (𝓞 K)) le_rfl] at h1
  exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K W)

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (S : Submodule K V) :
    Submodule.span K ((L ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun x hx => hx.2
  · intro v hv
    obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hL v
    have hc := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) s.2
    rw [← Submodule.smul_mem_iff _ hc]
    refine Submodule.subset_span ⟨?_, S.smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs

omit [StarRing K] [FiniteDimensional K V] in
theorem flat_of_submodule (D : Submodule (𝓞 K) V) : Module.Flat (𝓞 K) D := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro q ⟨a, ha⟩
  have h1 : (algebraMap (𝓞 K) K a) • (q : V) = 0 := by
    rw [algebraMap_smul]; exact congrArg Subtype.val ha
  have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
  rw [Submodule.mem_bot]
  exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h3)

section Proj

variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)

omit [NumberField K] [FiniteDimensional K V] in
include hU in
theorem integral {y x : V} (hy : y ∈ L) (hx : x ∈ L) : H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← hU.2, mem_dual_iff] at hy
  exact hy.2 x hx

omit [FiniteDimensional K V] in
include hU hp hq in

theorem proj_mem_dual {v : V} (hv : v ∈ L) : p v ∈ dual H (L ⊓ rs (𝓞 K) U) := by
  rw [mem_dual_iff, span_inf ((isLatMod_top_bot_iff L).1 hU.1)]
  refine ⟨hp v, fun a ha => ?_⟩
  have h0 := (mem_perp_iff H U _).1 (hq v) a ha.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
  rw [← h0]
  exact integral H hU hv ha.1

include hc hU hp hq in

theorem mem_dual_iff_proj (d : V) : d ∈ dual H (L ⊓ rs (𝓞 K) (perp H U)) ↔ ∃ v ∈ L, v - p v = d := by
  have hsp := span_inf ((isLatMod_top_bot_iff L).1 hU.1) (perp H U)
  have h0 : ∀ v, ∀ b ∈ perp H U, H.B b (p v) = 0 := fun v b hb => (mem_perp_iff H U _).1 hb _ (hp v)
  rw [mem_dual_iff, hsp]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H U)), IsIntegral ℤ (H.B x d) := by
      intro x
      rw [← GlobalTheory.UnimodQuot.mem_one_iff, ← H.herm]
      exact GlobalTheory.UnimodQuot.star_mem_one (hyM x x.2)
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H U)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x d, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) d = H.B a d + H.B b d
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) d = algebraMap (𝓞 K) K a * H.B b d
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨v, hv, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU (perp H U) φ
    refine ⟨v, hv, sub_eq_zero.1 ?_⟩
    have h1 : v - p v - d ∈ U := by
      apply GlobalTheory.UnimodQuot.mem_of_perp_perp H U
      intro x hx
      rw [← hsp] at hx
      have : Submodule.span K ((L ⊓ rs (𝓞 K) (perp H U) : Submodule (𝓞 K) V) : Set V) ≤
          LinearMap.ker (H.B.flip (v - p v - d)) := by
        rw [Submodule.span_le]
        intro b hb
        have h2 : H.B b v = H.B b d := h' ⟨b, hb⟩
        show H.B b (v - p v - d) = 0
        rw [map_sub, map_sub, h0 v b hb.2, h2, sub_zero, sub_self]
      exact this hx
    exact (Submodule.disjoint_def.1 hc.disjoint) _ h1 ((perp H U).sub_mem (hq v) hy)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨hq v, fun b hb => ?_⟩
    have : H.B (p v) b = 0 := by rw [← H.herm, h0 v b hb.2, star_zero]
    rw [map_sub, LinearMap.sub_apply, this, sub_zero]
    exact integral H hU hv hb.1

include hc hU in

theorem idx_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    idx (dual H (L ⊓ rs (𝓞 K) U)) (L ⊓ rs (𝓞 K) U) ≠ 0 := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  have hM : IsLatMod (L ⊓ rs (𝓞 K) U) U ⊥ := by
    refine ⟨⟨L ⊓ rs (𝓞 K) U, ?_, by simp⟩, span_inf hL U⟩
    have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) U) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  obtain ⟨h1, h2⟩ := (GlobalTheory.DegCnt.DelScale.main K V H hK _ _ U ⊥ bot_le (fun x hx =>
    ⟨fun h => (Submodule.disjoint_def.1 hc.disjoint) x hx ((mem_perp_iff H U x).2 h), by
      rintro rfl y _
      simp⟩) hM hM).2.2.2 ((isIntegralLat_iff H _).2 fun x hx y hy => integral H hU hx.1 hy.1)
  intro h
  rw [h] at h2
  have : (0 : ℝ) < del H (L ⊓ rs (𝓞 K) U) ^ 2 := by positivity
  rw [h2] at this
  simp at this

end Proj

theorem encard_gluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  intro K V _ _ _ _ _ _ _ _ H hK U A B x hc hx
  set S := {Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B} with hS
  rcases S.eq_empty_or_nonempty with h | ⟨L₀, hL₀, hA₀, hB₀⟩
  · rw [h]; simp
  obtain ⟨p, hp, hq⟩ : ∃ p : V →ₗ[K] V, (∀ v, p v ∈ U) ∧ ∀ v, v - p v ∈ perp H U :=
    ⟨U.projection _ hc, fun v => Submodule.projection_apply_mem hc v, fun v => Submodule.sub_projection_mem hc v⟩
  have hx0 : x ≠ 0 := by rw [← hx, ← hA₀]; exact idx_ne_zero H hc hL₀ hK
  have hpA : ∀ L ∈ S, ∀ v ∈ L, p v ∈ dual H A := fun L hL v hv => hL.2.1 ▸ proj_mem_dual H hL.1 hp hq hv
  have hD : ∀ L ∈ S, ∀ d, d ∈ dual H B ↔ ∃ v ∈ L, v - p v = d := fun L hL d =>
    hL.2.2 ▸ mem_dual_iff_proj H hc hL.1 hp hq d
  have hS₀ : L₀ ∈ S := ⟨hL₀, hA₀, hB₀⟩
  let q : V →ₗ[𝓞 K] V := (LinearMap.id - p).restrictScalars (𝓞 K)
  have hqv : ∀ v, q v = v - p v := fun _ => rfl
  have hfin : Module.Finite (𝓞 K) (dual H B) := by
    have e : dual H B = L₀.map q := by
      ext d; rw [hD L₀ hS₀]; rfl
    rw [e, Module.Finite.iff_fg]
    exact ((isLatMod_top_bot_iff L₀).1 hL₀.1).fg.map _
  have hflat := flat_of_submodule (dual H B)
  have hI : Ideal.span {(x : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hx0
  have := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨t, ht⟩ := exists_gens (𝓞 K) (dual H B) (Ideal.span {(x : 𝓞 K)})
  have hrk : Module.finrank (𝓞 K) (dual H B) ≤ Module.finrank K (perp H U) := by
    refine finrank_le fun d hd => ?_
    obtain ⟨v, -, rfl⟩ := (hD L₀ hS₀ d).1 hd
    exact hq v
  have hAL : ∀ L ∈ S, A ≤ L := fun L hL => hL.2.1 ▸ inf_le_left
  have hBL : ∀ L ∈ S, B ≤ L := fun L hL => hL.2.2 ▸ inf_le_left
  have hxB : ∀ d ∈ dual H B, (x : 𝓞 K) • d ∈ B := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (hD L₀ hS₀ d).1 hd
    have h1 : x • p v ∈ A := by
      have := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := (dual H A).toAddSubgroup) (hpA L₀ hS₀ v hv)
      rwa [show A.toAddSubgroup.relIndex (dual H A).toAddSubgroup = x from hx] at this
    rw [← hB₀]
    refine ⟨?_, (rs (𝓞 K) (perp H U)).smul_mem _ (hq v)⟩
    rw [Nat.cast_smul_eq_nsmul, smul_sub]
    exact L₀.sub_mem (nsmul_mem hv x) (hAL L₀ hS₀ h1)
  have hpB : ∀ b ∈ B, p b = 0 := by
    intro b hb
    rw [← hB₀] at hb
    refine (Submodule.disjoint_def.1 hc.disjoint) _ (hp b) ?_
    simpa using (perp H U).sub_mem hb.2 (hq b)
  choose w hw hw' using fun (L : S) i => (hD L L.2 (t i)).1 (t i).2
  let Q := (dual H A).toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf (dual H A).toAddSubgroup
  have hQ : Nat.card Q = x := hx
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hx0)
  let f : S → Fin (Module.finrank (𝓞 K) (dual H B)) → Q := fun L i =>
    QuotientAddGroup.mk ⟨p (w L i), hpA L L.2 _ (hw L i)⟩
  have key : ∀ L L' : S, f L = f L' → L.1 ≤ L'.1 := by
    intro L L' e v hv
    have h1 : ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype = ⊤ := by
      refine ht _ (fun i => ⟨w L i, ⟨hw L i, ?_⟩, hw' L i⟩) ?_
      · have h2 : -p (w L i) + p (w L' i) ∈ A := QuotientAddGroup.eq.1 (congrFun e i)
        have h3 : w L i = w L' i - (-p (w L i) + p (w L' i)) := by
          have := (hw' L i).trans (hw' L' i).symm
          linear_combination (norm := module) this
        rw [h3]
        exact L'.1.sub_mem (hw L' i) (hAL L' L'.2 h2)
      · refine Submodule.smul_le.2 fun r hr d _ => ?_
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h2 : (c * x) • (d : V) ∈ B := by rw [mul_smul]; exact B.smul_mem _ (hxB d d.2)
        refine ⟨(c * x) • (d : V), ⟨hBL L L.2 h2, hBL L' L'.2 h2⟩, ?_⟩
        rw [hqv, hpB _ h2, sub_zero]; rfl
    have h2 : (⟨v - p v, (hD L L.2 _).2 ⟨v, hv, rfl⟩⟩ : dual H B) ∈
        ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype := h1 ▸ Submodule.mem_top
    obtain ⟨u, ⟨hu, hu'⟩, e'⟩ := h2
    have e'' : u - p u = v - p v := e'
    have h3 : v - u ∈ A := by
      rw [← L.2.2.1]
      refine ⟨L.1.sub_mem hv hu, ?_⟩
      have : v - u = p v - p u := by linear_combination (norm := module) -e''
      rw [this]
      exact U.sub_mem (hp v) (hp u)
    simpa using L'.1.add_mem (hAL L' L'.2 h3) hu'
  have hf : Function.Injective f := fun L L' e => Subtype.ext (le_antisymm (key L L' e) (key L' L e.symm))
  have : Finite S := Finite.of_injective f hf
  have h1 : Nat.card S ≤ x ^ Module.finrank K (perp H U) := by
    refine (Nat.card_le_card_of_injective f hf).trans ?_
    rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx0) hrk
  rw [← (Set.toFinite S).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h1

end GlobalTheory.DegCnt.Glue
