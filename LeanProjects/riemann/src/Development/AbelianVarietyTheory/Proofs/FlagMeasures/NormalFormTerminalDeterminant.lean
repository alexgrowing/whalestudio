import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFlagPairLatticeSumDiscriminantEqNormMinorStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitIdx

open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale

section General

variable {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

theorem idx_congr {A B C : Submodule R W} (h : A ⊓ B = A ⊓ C) : idx A B = idx A C := by
  rw [← idx_inf_left A B, h, idx_inf_left]

theorem idx_comap (f : W →ₗ[R] W') (A : Submodule R W) (B : Submodule R W') :
    idx A (B.comap f) = idx (A.map f) B :=
  AddSubgroup.relIndex_comap B.toAddSubgroup f.toAddMonoidHom A.toAddSubgroup

theorem idx_of_bij (f : W →+ W) (hf : Function.Bijective f) {A B A' B' : Submodule R W}
    (hA : ∀ x, f x ∈ A' ↔ x ∈ A) (hB : ∀ x, f x ∈ B' ↔ x ∈ B) : idx A' B' = idx A B := by
  have key : ∀ {C C' : Submodule R W}, (∀ x, f x ∈ C' ↔ x ∈ C) → C'.toAddSubgroup = C.toAddSubgroup.map f := by
    intro C C' h
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [AddSubgroup.mem_map]
    exact ⟨fun hx => ⟨x, (h x).1 hx, rfl⟩, fun ⟨z, hz, e⟩ => e ▸ (h z).2 hz⟩
  unfold idx
  rw [key hA, key hB]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf.1

theorem gidx_eq_idx {A B : Submodule R W} (h : B ≤ A) : gidx A B = idx A B := by
  rw [gidx, idx_eq B, idxN_eq_one.2 h]; simp

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_mul {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (x : V) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) • x ∈ Λ := by
  refine ⟨_, idxN_ne_zero hΛ (Submodule.fg_span_singleton x), ?_⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem Λ.toAddSubgroup
    (K := (Submodule.span (𝓞 K) {x}).toAddSubgroup) (Submodule.mem_span_singleton_self x)

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (S : Submodule K V) :
    Submodule.span K ((Λ ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun x hx => ?_
  obtain ⟨n, hn, h⟩ := exists_mul hΛ x
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  have : x = (n : K)⁻¹ • ((n : K) • x) := by rw [smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, S.smul_mem _ hx⟩)

omit [StarRing K] in
theorem isLattice_field {M : Submodule (𝓞 K) K} (hfg : M.FG) {x : K} (hx : x ∈ M) (h0 : x ≠ 0) :
    Submodule.IsLattice K M := by
  refine ⟨hfg, eq_top_iff.2 fun y _ => ?_⟩
  have : y = (y * x⁻¹) • x := by simp [h0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem idx_scal {c : K} (hc : c * star c = 1) {A M M' : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M') (h : ∀ t, t ∈ M' ↔ t * c ∈ M)
    (h1 : M ≤ A) (h2 : M' ≤ A) : idx A M' = idx A M := by
  have hc0 : c ≠ 0 := fun e => by simp [e] at hc
  have hone : (1 : Submodule (𝓞 K) K).FG := by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have o1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have L1 := isLattice_field hone o1 one_ne_zero
  set C : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {c} with hC
  have LC : Submodule.IsLattice K C :=
    isLattice_field (Submodule.fg_span_singleton _) (Submodule.mem_span_singleton_self c) hc0
  have mC : ∀ x : K, x * c ∈ C ↔ x ∈ (1 : Submodule (𝓞 K) K) := fun x => by
    rw [hC, Submodule.mem_span_singleton, Submodule.mem_one]
    refine exists_congr fun a => ?_
    rw [Algebra.smul_def, mul_left_inj' hc0]
  have ms : ∀ x : K, star x ∈ (1 : Submodule (𝓞 K) K) ↔ x ∈ (1 : Submodule (𝓞 K) K) := by
    have : ∀ x : K, x ∈ (1 : Submodule (𝓞 K) K) → star x ∈ (1 : Submodule (𝓞 K) K) := fun x hx => by
      obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hx
      exact Submodule.mem_one.2 (Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range a)
    exact fun x => ⟨fun hx => by simpa using this _ hx, this x⟩
  have bm : Function.Bijective (AddMonoidHom.mulRight c) := (Equiv.mulRight₀ c hc0).bijective
  set f : K →+ K := (AddMonoidHom.mulRight c).comp (starAddEquiv : K ≃+ K).toAddMonoidHom with hf
  have fx : ∀ x, f x = star x * c := fun _ => rfl
  have bf : Function.Bijective f := bm.comp (starAddEquiv : K ≃+ K).bijective
  have e1 : idx C 1 = idx 1 C := by
    refine idx_of_bij f bf (fun x => by rw [fx, mC, ms]) fun x => ?_
    rw [fx, ← ms, star_mul, star_star, ← mC]
    have : star c * x * c = x := by rw [mul_right_comm, mul_comm (star c), hc, one_mul]
    rw [this]
  have g1 : gidx C 1 = 1 := by
    rw [gidx, e1]
    exact div_self (Nat.cast_ne_zero.2 (idxN_ne_zero LC hone))
  have g2 : gidx M C = gidx M' 1 := by
    rw [gidx, gidx, idx_of_bij _ bm (A := M') (B := 1) (fun x => (h x).symm) mC,
      idx_of_bij _ bm (A := 1) (B := M') mC (fun x => (h x).symm)]
  have g3 : gidx M 1 = gidx M' 1 := by rw [← gidx_mul hM LC L1, g1, mul_one, g2]
  have a := gidx_mul hA hM L1
  have b := gidx_mul hA hM' L1
  rw [g3, ← b, mul_left_inj' (gidx_pos hM' L1).ne', gidx_eq_idx h1, gidx_eq_idx h2] at a
  exact_mod_cast a.symm

section Flag

variable {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_mono (F : FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (Set.image_mono fun _ hx => lt_of_lt_of_le hx h)

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem (F : FlagD H r) {a : Fin r} {b : ℕ} (h : a.val < b) : F.e a.castSucc ∈ F.Xa b :=
  Submodule.subset_span ⟨a, h, rfl⟩

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_Xa_succ (F : FlagD H r) (a : Fin r) {x : V} (hx : x ∈ F.Xa (a.val + 1)) :
    ∃ t : K, x - t • F.e a.castSucc ∈ F.Xa a.val := by
  have : F.Xa (a.val + 1) ≤ F.Xa a.val ⊔ Submodule.span K {F.e a.castSucc} := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · exact Submodule.mem_sup_left (e_mem F h)
    · obtain rfl : b = a := Fin.ext h
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (this hx)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by simpa using hy⟩

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem iso_X (F : FlagD H r) {x y : V} (hx : x ∈ F.X) (hy : y ∈ F.X ⊔ Submodule.span K {F.z}) :
    H.B y x = 0 := by
  have h1 : ∀ a : Fin r, ∀ y ∈ F.X ⊔ Submodule.span K {F.z}, H.B y (F.e a.castSucc) = 0 := by
    intro a y hy
    have : F.X ⊔ Submodule.span K {F.z} ≤ LinearMap.ker (H.B.flip (F.e a.castSucc)) := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨b, -, rfl⟩
        exact F.iso b a
      · rintro _ rfl
        change H.B F.z _ = 0
        rw [← H.herm, FlagD.z, F.zperp, star_zero]
    exact this hy
  have : F.X ≤ LinearMap.ker (H.B y) := Submodule.span_le.2 (by
    rintro _ ⟨b, -, rfl⟩
    exact h1 b y hy)
  exact this hx

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem level_lt (F : FlagD H r) {x : V} {b : Fin r} {al : K} (h : F.HasLevel x b al) {a : ℕ}
    (hx : x ∈ F.Xa a) : b.val < a := by
  by_contra hlt
  have h1 : al • F.e b.castSucc ∈ F.Xa b.val := by
    simpa using Submodule.sub_mem _ (Xa_mono F (not_lt.1 hlt) hx) h.2
  rw [Submodule.smul_mem_iff _ h.1] at h1
  exact F.indep.notMem_span_image (s := {c : Fin r | c.val < b.val}) (by simp) h1

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_of_level (F : FlagD H r) {x : V} {b : Fin r} {al : K} (h : F.HasLevel x b al) {a : ℕ}
    (hb : b.val < a) : x ∈ F.Xa a := by
  simpa using Submodule.add_mem _ (Xa_mono F hb.le h.2) (Submodule.smul_mem _ al (e_mem F hb))

omit [NumberField K] [FiniteDimensional K V] in
theorem mem_lead (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (a : Fin r) (t : K) :
    t ∈ lead F Λ a.castSucc ↔ ∃ x ∈ Λ, x - t • F.e a.castSucc ∈ F.Xa a.val := by
  change t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val) ↔ _
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, y, hy, e⟩
    exact ⟨x, hx, by rw [← e]; simpa using (F.Xa a.val).neg_mem hy⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, _, (F.Xa a.val).neg_mem h, by abel⟩

omit [NumberField K] [FiniteDimensional K V] in

theorem step (F : FlagD H r) {Λ J : Submodule (𝓞 K) V} (hJ : J ≤ Λ) (a : Fin r) :
    idx (latF F Λ (a.val + 1) ⊔ J) (latF F Λ a.val ⊔ J) = idx (lead F Λ a.castSucc) (lead F J a.castSucc) := by
  rw [idx_sup le_sup_right]
  have e : idx (lead F Λ a.castSucc) (lead F J a.castSucc) = _ := idx_comap _ _ (J ⊔ rs (𝓞 K) (F.Xa a.val))
  rw [e, ← idx_sup (I := rs (𝓞 K) (F.Xa a.val)) (B := J ⊔ _) le_sup_right]
  have e2 : (lead F Λ a.castSucc).map ((LinearMap.toSpanSingleton K V (F.e a.castSucc)).restrictScalars (𝓞 K)) ⊔
      rs (𝓞 K) (F.Xa a.val) = latF F Λ (a.val + 1) ⊔ rs (𝓞 K) (F.Xa a.val) := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨x, hx, h⟩ := (mem_lead F Λ a t).1 ht
      refine Submodule.mem_sup.2 ⟨x, ⟨hx, ?_⟩, _, (F.Xa a.val).neg_mem h, ?_⟩
      · change x ∈ F.Xa (a.val + 1)
        simpa using Submodule.add_mem _ (Xa_mono F (Nat.le_succ _) h)
          (Submodule.smul_mem _ t (e_mem F (Nat.lt_succ_self a.val)))
      · change _ = t • F.e a.castSucc
        abel
    · rintro x ⟨hx, hx'⟩
      obtain ⟨t, ht⟩ := mem_Xa_succ F a hx'
      refine Submodule.mem_sup.2 ⟨_, ⟨t, (mem_lead F Λ a t).2 ⟨x, hx, ht⟩, rfl⟩, _, ht, ?_⟩
      change t • F.e a.castSucc + _ = _
      abel
  rw [e2, idx_sup le_sup_right]
  refine idx_congr (le_antisymm (inf_le_inf_left _ (sup_le (le_sup_of_le_right inf_le_right) le_sup_left)) ?_)
  rintro x ⟨hx, h⟩
  obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨hx, ?_⟩
  rw [add_comm]
  exact Submodule.add_mem_sup ⟨by simpa using Λ.sub_mem hx.1 (hJ hi), hy⟩ hi

omit [NumberField K] [FiniteDimensional K V] in
theorem idx_side (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) {j : ℕ} (hj : j ≤ r) {P : Submodule (𝓞 K) V}
    (h1 : P ≤ rs (𝓞 K) F'.X) (h2 : rs (𝓞 K) (II F F') ≤ P) :
    idx ((Λ ⊓ rs (𝓞 K) F.X) ⊔ P) (latF F Λ j ⊔ P) = bOne F F' Λ j := by
  rw [idx_sup le_sup_right]
  refine idx_congr (le_antisymm ?_ (inf_le_inf_left _ (sup_le_sup_left (inf_le_right.trans h2) _)))
  rintro x ⟨hx, h⟩
  obtain ⟨y, hy, p, hp, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨hx, Submodule.add_mem_sup hy ⟨by simpa using Λ.sub_mem hx.1 hy.1, ?_, h1 hp⟩⟩
  simpa using F.X.sub_mem hx.2 (Xa_mono F hj hy.2)

end Flag

omit [FiniteDimensional K V] in

theorem del_sup (H : HermSpace K V) (M : Submodule (𝓞 K) V) (I : Submodule K V)
    (h0 : I ⊓ Submodule.span K (M : Set V) = ⊥)
    (hI : ∀ i ∈ I, ∀ y ∈ Submodule.span K (M : Set V) ⊔ I, H.B i y = 0) :
    del H (M ⊔ rs (𝓞 K) I) = del H M := by
  have hs : Submodule.span K ((M ⊔ rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V) = Submodule.span K (M : Set V) ⊔ I := by
    refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (sup_le (Submodule.span_mono (le_sup_left (a := M)))
      fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx))
    obtain ⟨m, hm, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.add_mem_sup (Submodule.subset_span hm) hi
  have hI' : ∀ i ∈ I, ∀ y ∈ Submodule.span K (M : Set V) ⊔ I, H.B y i = 0 := fun i hi y hy => by
    rw [← H.herm, hI i hi y hy, star_zero]
  have hd : dual H (M ⊔ rs (𝓞 K) I) = dual H M ⊔ rs (𝓞 K) I := by
    ext y
    rw [mem_dual_iff, hs]
    constructor
    · rintro ⟨hy, h⟩
      obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      refine Submodule.add_mem_sup ((mem_dual_iff H M s).2 ⟨hs, fun x hx => ?_⟩) hi
      have := h x (Submodule.mem_sup_left hx)
      rwa [map_add, LinearMap.add_apply, hI i hi x (Submodule.mem_sup_left (Submodule.subset_span hx)),
        add_zero] at this
    · intro hy
      obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      rw [mem_dual_iff] at hs
      refine ⟨Submodule.add_mem_sup hs.1 hi, fun x hx => ?_⟩
      obtain ⟨m, hm, i', hi', rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, hI' i' hi' _ (Submodule.add_mem_sup hs.1 hi), add_zero, map_add, LinearMap.add_apply,
        hI i hi m (Submodule.mem_sup_left (Submodule.subset_span hm)), add_zero]
      exact hs.2 m hm
  have key : ∀ {A B : Submodule (𝓞 K) V}, A ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) →
      B ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) → idx (A ⊔ rs (𝓞 K) I) (B ⊔ rs (𝓞 K) I) = idx A B := by
    intro A B hA hB
    rw [idx_sup le_sup_right]
    refine idx_congr (le_antisymm ?_ (inf_le_inf_left _ le_sup_left))
    rintro x ⟨hx, h⟩
    obtain ⟨b, hb, i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have : i ∈ I ⊓ Submodule.span K (M : Set V) :=
      ⟨hi, by simpa using (Submodule.span K (M : Set V)).sub_mem (hA hx) (hB hb)⟩
    rw [h0, Submodule.mem_bot] at this
    subst this
    exact ⟨hx, by simpa using hb⟩
  have a : M ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) := fun x hx => Submodule.subset_span hx
  have b : dual H M ≤ rs (𝓞 K) (Submodule.span K (M : Set V)) := inf_le_left
  rw [del, del, hd, gidx, gidx, key a b, key b a]

theorem bOne_symm (H : HermSpace K V) {r : ℕ} (N : NF H r) (hS : NFShape N.F N.F' N.j N.c)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hF : IsFrame N.F Λ N.aa) (hF' : IsFrame N.F' Λ N.aa) :
    bOne N.F' N.F Λ N.j = bOne N.F N.F' Λ N.j := by
  obtain ⟨hc0, -, hlev, -⟩ := hS
  set J := Λ ⊓ rs (𝓞 K) (II N.F N.F') with hJ
  have hX : ∀ x ∈ II N.F N.F', ∀ a, x ∈ N.F.Xa a ↔ x ∈ N.F'.Xa a := by
    intro x hx a
    by_cases h0 : x = 0
    · simp [h0]
    obtain ⟨b, al, al', h1, h2, -⟩ := hlev x hx h0
    exact ⟨fun h => mem_of_level _ h2 (level_lt _ h1 h), fun h => mem_of_level _ h1 (level_lt _ h2 h)⟩
  have one : ∀ a : Fin r, N.j ≤ a.val → idx (lead N.F' Λ a.castSucc) (lead N.F' J a.castSucc) =
      idx (lead N.F Λ a.castSucc) (lead N.F J a.castSucc) := by
    intro a ha
    have he : N.F'.e a.castSucc = N.c • N.F.e a.castSucc := N.same _ ha
    have hI : N.F.e a.castSucc ∈ II N.F N.F' := ⟨e_mem _ a.2, by
      have := e_mem N.F' a.2
      rwa [he, Submodule.smul_mem_iff _ hc0] at this⟩
    have l1 : lead N.F J a.castSucc ≤ N.aa a := hF.1 a ▸ Submodule.comap_mono (sup_le_sup_right inf_le_left _)
    have l2 : lead N.F' J a.castSucc ≤ N.aa a := hF'.1 a ▸ Submodule.comap_mono (sup_le_sup_right inf_le_left _)
    have hfg : (N.aa a).FG := (isNoetherian_submodule.1 (FractionalIdeal.isNoetherian _)) _ le_rfl
    have hm : ∀ t, t ∈ lead N.F' J a.castSucc ↔ t * N.c ∈ lead N.F J a.castSucc := fun t => by
      rw [mem_lead, mem_lead, he, smul_smul]
      refine exists_congr fun x => and_congr_right fun hx => (hX _ ?_ _).symm
      exact Submodule.sub_mem _ hx.2 (Submodule.smul_mem _ _ hI)
    obtain ⟨n, hn, h⟩ := exists_mul hΛ (N.F.e a.castSucc)
    have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
    have m1 : (n : K) ∈ lead N.F J a.castSucc :=
      (mem_lead _ _ _ _).2 ⟨_, ⟨h, Submodule.smul_mem _ _ hI⟩, by simp⟩
    have m2 : (n : K) * N.c⁻¹ ∈ lead N.F' J a.castSucc := by
      rw [hm]; simpa [hc0] using m1
    rw [hF.1, hF'.1]
    exact idx_scal N.c_norm (isLattice_field hfg (l1 m1) hn') (isLattice_field (hfg.of_le l1) m1 hn')
      (isLattice_field (hfg.of_le l2) m2 (mul_ne_zero hn' (inv_ne_zero hc0))) hm l1 l2
  have mono : ∀ (F : FlagD H r) {a b : ℕ}, a ≤ b → latF F Λ a ⊔ J ≤ latF F Λ b ⊔ J := fun F a b h =>
    sup_le_sup_right (inf_le_inf_left _ (fun x hx => Xa_mono F h hx)) _
  have all : ∀ m, N.j ≤ m → m ≤ r → idx (latF N.F' Λ m ⊔ J) (latF N.F' Λ N.j ⊔ J) =
      idx (latF N.F Λ m ⊔ J) (latF N.F Λ N.j ⊔ J) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; simp [idx]
    | succ m hm ih =>
      intro h
      rw [← idx_mul (mono N.F' hm) (mono N.F' (Nat.le_succ m)), ← idx_mul (mono N.F hm) (mono N.F (Nat.le_succ m)),
        ih (Nat.le_of_succ_le h)]
      congr 1
      exact (step N.F' inf_le_left ⟨m, h⟩).trans ((one ⟨m, h⟩ hm).trans (step N.F inf_le_left ⟨m, h⟩).symm)
  have := all r N.j_le le_rfl
  rw [idx_sup le_sup_right, idx_sup le_sup_right] at this
  rw [bOne, bOne, show II N.F' N.F = II N.F N.F' from inf_comm _ _]
  exact this

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.bI Λ ≠ 0 ∧ bOne N.F' N.F Λ N.j = N.bI Λ ∧ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 = N.Del ∧ 1 ≤ delBar N.F N.F' Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT
  have G := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hD := (GlobalTheory.T.hermFlagPairLatticeSumDiscriminant_eq_norm_minor K V H hK r N g Λ hg hT N.j le_rfl G.2.2.2.2.2.2.2.2.2.2.1).1
  obtain ⟨hS, -, -, hrad, -⟩ := G.1
  obtain ⟨⟨hU, hF, hF'⟩, -⟩ := hT
  have hΛ := ((isUnimod_iff H Λ).1 hU).1
  have hb := bOne_symm H N hS hΛ hF hF'
  obtain ⟨hc0, -, -, -, z1, z2, x1, x2, hz⟩ := hS
  have hII : II N.F' N.F = II N.F N.F' := inf_comm _ _
  set I := II N.F N.F' with hI
  set S := N.F.X ⊔ N.F'.X with hSd
  have hIS : I ≤ S := le_sup_of_le_left inf_le_left
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi y hy =>
    (hrad i (Submodule.mem_sup_left (hIS hi))).2 hi y (Submodule.mem_sup_left hy)
  have hr : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I := by
    refine fun v hv => ⟨fun h => (hrad v (Submodule.mem_sup_left hv)).1 ?_, fun h => o1 v h⟩
    obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.1 hv
    have sw : ∀ a b : V, H.B a b = 0 → H.B b a = 0 := fun a b e => by rw [← H.herm, e, star_zero]
    have a : ∀ y ∈ S, H.B y x' = 0 := fun y hy => by
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
      have := h u (Submodule.mem_sup_left hu)
      rw [map_add, LinearMap.add_apply, iso_X N.F hu (Submodule.mem_sup_left hx), zero_add] at this
      rw [map_add, LinearMap.add_apply, sw _ _ this, iso_X N.F' hx' (Submodule.mem_sup_left hu'), zero_add]
    have b := a _ hz
    rw [map_sub, LinearMap.sub_apply, iso_X N.F' hx' (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
      map_smul, LinearMap.smul_apply, zero_sub, neg_eq_zero, smul_eq_mul, mul_eq_zero, or_iff_right hc0] at b
    have c : H.B N.F.z (x + x') = 0 := by
      rw [map_add, b, iso_X N.F hx (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)), add_zero]
    have d := sw _ _ (h _ hz)
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, c, smul_zero, sub_zero] at d
    intro w hw
    apply sw
    have : V0 N.F N.F' ≤ LinearMap.ker (H.B.flip (x + x')) := by
      refine sup_le (fun y hy => sw _ _ (h y hy)) (Submodule.span_le.2 ?_)
      rintro _ (rfl | rfl)
      · exact c
      · exact d
    exact this hw
  have spI : Submodule.span K ((rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V) = I := Submodule.span_eq I
  have spS : ∀ A B : Submodule (𝓞 K) V, Submodule.span K ((A ⊔ B : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊔ Submodule.span K (B : Set V) := fun A B => by
    refine le_antisymm (Submodule.span_le.2 fun x hx => ?_)
      (sup_le (Submodule.span_mono (le_sup_left (a := A))) (Submodule.span_mono (le_sup_right (b := B))))
    obtain ⟨m, hm, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.add_mem_sup (Submodule.subset_span hm) (Submodule.subset_span hi)
  set M := latF N.F Λ N.j ⊔ latF N.F' Λ N.j with hM
  set A := Λ ⊓ rs (𝓞 K) N.F.X with hA
  set A' := Λ ⊓ rs (𝓞 K) N.F'.X with hA'
  have spM : Submodule.span K (M : Set V) = N.F.Xa N.j ⊔ N.F'.Xa N.j := by
    rw [hM, spS, latF, latF, span_inf hΛ, span_inf hΛ]
  have spM' : Submodule.span K (M : Set V) ⊔ I = S := by
    rw [spM, hSd, x1, x2, sup_sup_sup_comm, sup_idem]
  have eB : latA0 N.F N.F' Λ ⊔ latA0 N.F' N.F Λ = (A ⊔ A') ⊔ rs (𝓞 K) I := by
    rw [latA0, latA0, hII, sup_sup_sup_comm, sup_idem]
  have L1 : IsLatMod ((A ⊔ A') ⊔ rs (𝓞 K) I) S I :=
    ⟨⟨_, hΛ.fg.of_le (sup_le inf_le_left inf_le_left), rfl⟩, by
      rw [spS, spS, spI, span_inf hΛ, span_inf hΛ]; exact sup_eq_left.2 hIS⟩
  have L2 : IsLatMod (M ⊔ rs (𝓞 K) I) S I :=
    ⟨⟨_, hΛ.fg.of_le (sup_le inf_le_left inf_le_left), rfl⟩, by rw [spS, spI, spM']⟩
  have hint : IsIntegralLat H ((A ⊔ A') ⊔ rs (𝓞 K) I) := by
    rw [isIntegralLat_iff]
    intro x hx y hy
    obtain ⟨m, hm, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨m', hm', i', hi', rfl⟩ := Submodule.mem_sup.1 hy
    have lS : A ⊔ A' ≤ rs (𝓞 K) S := sup_le (fun x hx => Submodule.mem_sup_left (S := N.F.X) hx.2)
      (fun x hx => Submodule.mem_sup_right (T := N.F'.X) hx.2)
    have lΛ : A ⊔ A' ≤ Λ := sup_le inf_le_left inf_le_left
    rw [map_add H.B m i, LinearMap.add_apply, o1 i hi _ (S.add_mem (lS hm') (hIS hi')), add_zero, map_add,
      ← H.herm i' m, o1 i' hi' m (lS hm), star_zero, add_zero]
    have : m ∈ dual H Λ := hU.2.symm ▸ lΛ hm
    exact ((mem_dual_iff H Λ m).1 this).2 m' (lΛ hm')
  obtain ⟨-, p2, p3, p4⟩ := DelScale.main K V H hK _ _ S I hIS hr L1 L2
  have f1 : latF N.F Λ N.j ≤ A := inf_le_inf_left _ fun x hx => Xa_mono N.F N.j_le hx
  have f2 : latF N.F' Λ N.j ≤ A' := inf_le_inf_left _ fun x hx => Xa_mono N.F' N.j_le hx
  have i1 := idx_side N.F N.F' Λ N.j_le (P := latF N.F' Λ N.j ⊔ rs (𝓞 K) I)
    (sup_le (f2.trans inf_le_right) fun x hx => hx.2) le_sup_right
  have i2 := idx_side N.F' N.F Λ N.j_le (P := A ⊔ rs (𝓞 K) I)
    (sup_le inf_le_right fun x hx => hx.1) (hII ▸ le_sup_right)
  have ei : idx ((A ⊔ A') ⊔ rs (𝓞 K) I) (M ⊔ rs (𝓞 K) I) = N.bI Λ * N.bI Λ := by
    rw [← idx_mul (B := A ⊔ (latF N.F' Λ N.j ⊔ rs (𝓞 K) I))
      (by rw [hM, sup_assoc]; exact sup_le_sup_right f1 _)
      (by rw [sup_assoc]; exact sup_le_sup_left (sup_le_sup_right f2 _) _), hM, sup_assoc, i1,
      sup_left_comm A, sup_comm A A', sup_assoc, i2, hb]
    rfl
  rw [gidx_eq_idx (sup_le_sup_right (sup_le_sup f1 f2) _), ei] at p2 p3
  have h0 : I ⊓ Submodule.span K (M : Set V) = ⊥ := by
    rw [spM, eq_bot_iff]
    rintro i ⟨hi, h⟩
    obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.1 h
    have a : x ∈ I ⊓ N.F.Xa N.j := ⟨⟨Xa_mono N.F N.j_le hx, by
      simpa using N.F'.X.sub_mem hi.2 (Xa_mono N.F' N.j_le hx')⟩, hx⟩
    rw [z1, Submodule.mem_bot] at a
    subst a
    exact z2 ▸ ⟨hi, by simpa using hx'⟩
  rw [del_sup H M I h0 (by rw [spM']; exact o1)] at p3
  refine ⟨fun e => by simp [e] at p2, hb, ?_, ?_⟩
  · rw [delBar, eB, NF.Del, ← hD, normD, p3]
    push_cast
    ring
  · rw [delBar, eB]
    exact (p4 hint).1

end GlobalTheory.DegCnt.SplitIdx
