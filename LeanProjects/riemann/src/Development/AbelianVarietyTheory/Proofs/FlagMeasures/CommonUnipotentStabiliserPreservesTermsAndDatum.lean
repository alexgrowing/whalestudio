import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.StabInv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

structure Keeps (F : FlagD H r) (s : V ≃ₗ[K] V) : Prop where
  iso : ∀ x y, H.B (s x) (s y) = H.B x y
  flag : ∀ (a : ℕ) (x : V), s x ∈ F.Xa a ↔ x ∈ F.Xa a
  vec : ∀ a : Fin (r + 1), s (F.e a) - F.e a ∈ F.Xa a.val
  mid : ∀ y : V, (∀ x ∈ F.X, H.B y x = 0) → s y - y ∈ F.X

section Group
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Keeps.flagX {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (x : V) :
    s x ∈ F.X ↔ x ∈ F.X := h.flag r x

theorem keeps_one (F : FlagD H r) : Keeps F 1 :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl, fun a => by simp, fun y _ => by simp⟩

theorem Keeps.mul {F : FlagD H r} {s t : V ≃ₗ[K] V} (hs : Keeps F s) (ht : Keeps F t) :
    Keeps F (s * t) := by
  refine ⟨fun x y => ?_, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · simp [hs.iso, ht.iso]
  · simp [hs.flag, ht.flag]
  · have h1 := (hs.flag _ _).2 (ht.vec a)
    have h2 := add_mem h1 (hs.vec a)
    simpa using h2
  · have h1 := (hs.flagX _).2 (ht.mid y hy)
    have h2 := add_mem h1 (hs.mid y hy)
    simpa using h2

theorem apply_inv (s : V ≃ₗ[K] V) (x : V) : s (s⁻¹ x) = x := s.apply_symm_apply x

theorem Keeps.inv {F : FlagD H r} {s : V ≃ₗ[K] V} (hs : Keeps F s) : Keeps F s⁻¹ := by
  refine ⟨fun x y => ?_, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · rw [← hs.iso, apply_inv, apply_inv]
  · rw [← hs.flag, apply_inv]
  · rw [← hs.flag, map_sub, apply_inv]
    simpa using neg_mem (hs.vec a)
  · rw [← hs.flagX, map_sub, apply_inv]
    simpa using neg_mem (hs.mid y hy)

theorem xa_mono (F : FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (Set.image_mono fun _ hc => lt_of_lt_of_le hc h)

theorem keeps_of_inN [FiniteDimensional K V] {F : FlagD H r} {s : V ≃ₗ[K] V}
    (h : F.InN (s : V →ₗ[K] V)) : Keeps F s := by
  obtain ⟨h1, -, h3, h4⟩ := h
  have hmem : ∀ b : Fin r, F.e b.castSucc ∈ F.X := fun b =>
    Submodule.subset_span ⟨b, b.2, rfl⟩
  refine ⟨h1, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · have hle : (F.Xa a).map (s : V →ₗ[K] V) ≤ F.Xa a := by
      rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb1 : F.e b.castSucc ∈ F.Xa a := Submodule.subset_span ⟨b, hb, rfl⟩
      have hb2 := xa_mono F (le_of_lt hb) (h3 b)
      simpa using add_mem hb2 hb1
    have heq : (F.Xa a).map (s : V →ₗ[K] V) = F.Xa a :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s _)
    constructor
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rwa [← s.injective hxy]
    · intro hx
      exact hle ⟨x, hx, rfl⟩
  · induction a using Fin.lastCases with
    | last => exact h4 _ F.zperp
    | cast b => exact h3 b
  · refine h4 y fun b => ?_
    rw [← H.herm, hy _ (hmem b), star_zero]

end Group

theorem keeps_of_mem [FiniteDimensional K V] (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.R) :
    Keeps N.F s ∧ Keeps N.F' s := by
  unfold NF.R at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact ⟨keeps_of_inN hx.1, keeps_of_inN hx.2⟩
  | one => exact ⟨keeps_one _, keeps_one _⟩
  | mul x y _ _ hx hy => exact ⟨hx.1.mul hy.1, hx.2.mul hy.2⟩
  | inv x _ hx => exact ⟨hx.1.inv, hx.2.inv⟩

omit [StarRing K] in
theorem apply_mem_smul (s : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Λ) :
    s x ∈ s • Λ := Submodule.smul_mem_pointwise_smul x s Λ hx

omit [StarRing K] in
theorem exists_of_mem_smul {s : V ≃ₗ[K] V} {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ s • Λ) :
    ∃ y ∈ Λ, s y = x := (Submodule.mem_smul_pointwise_iff_exists x s Λ).1 hx

omit [StarRing K] in
theorem apply_mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) :
    s x ∈ s • Λ ↔ x ∈ Λ := by
  refine ⟨fun h => ?_, apply_mem_smul s⟩
  obtain ⟨y, hy, hxy⟩ := exists_of_mem_smul h
  rwa [← s.injective hxy]

omit [StarRing K] in
theorem apply_mem_smulLat (s : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} (g : 𝓞 K) {x : V}
    (hx : x ∈ smulLat g Λ) : s x ∈ smulLat g (s • Λ) := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨s y, apply_mem_smul s hy, ?_⟩
  show g • s y = s (g • y)
  rw [← algebraMap_smul K g y, map_smul, algebraMap_smul]

theorem lead_le {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (Λ : Submodule (𝓞 K) V)
    (a : Fin (r + 1)) : lead F Λ a ≤ lead F (s • Λ) a := by
  intro t ht
  obtain ⟨l, hl, x, hx, he⟩ := Submodule.mem_sup.1 ht
  have he' : l + x = t • F.e a := he
  refine Submodule.mem_sup.2 ⟨s l, apply_mem_smul s hl, s x - t • (s (F.e a) - F.e a),
    sub_mem ((h.flag _ _).2 hx) (Submodule.smul_mem (F.Xa a.val) t (h.vec a)), ?_⟩
  show _ = t • F.e a
  rw [smul_sub, ← map_smul, ← he', map_add]
  abel

theorem lead_eq {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (Λ : Submodule (𝓞 K) V)
    (a : Fin (r + 1)) : lead F (s • Λ) a = lead F Λ a := by
  refine le_antisymm ?_ (lead_le h Λ a)
  simpa using lead_le h.inv (s • Λ) a

theorem isFrame_smul {F : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) {Λ : Submodule (𝓞 K) V}
    {aa : Fin r → Submodule (𝓞 K) K} (hΛ : IsFrame F Λ aa) : IsFrame F (s • Λ) aa :=
  ⟨fun a => by rw [lead_eq h, hΛ.1], by rw [lead_eq h, hΛ.2]⟩

theorem isAdm_smul {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    {Λ : Submodule (𝓞 K) V} {g : 𝓞 K} (hΛ : IsAdm F F' Λ g) : IsAdm F F' (s • Λ) g := by
  intro a t x' hx' hx
  obtain ⟨l', hl', rfl⟩ := exists_of_mem_smul hx'
  have h1 : l' - t • F'.e a ∈ F'.Xa a.val := by
    rw [← h'.flag]
    have := sub_mem hx (Submodule.smul_mem _ t (h'.vec a))
    convert this using 1
    rw [map_sub, map_smul, smul_sub]
    abel
  obtain ⟨l, hl, h2, h3⟩ := hΛ a t l' hl' h1
  refine ⟨s l, apply_mem_smul s hl, ?_, ?_⟩
  · have := add_mem ((h.flag _ _).2 h2) (Submodule.smul_mem _ t (h.vec a))
    convert this using 1
    rw [map_sub, map_smul, smul_sub]
    abel
  · rw [← map_sub]
    exact apply_mem_smulLat s g h3

theorem isUnimod_smul {s : V ≃ₗ[K] V} (h : ∀ x y, H.B (s x) (s y) = H.B x y)
    {Λ : Submodule (𝓞 K) V} (hΛ : IsUnimod H Λ) : IsUnimod H (s • Λ) := by
  obtain ⟨h1, h2⟩ := hΛ
  have hL := (isLatMod_top_bot_iff Λ).1 h1
  have hspan : Submodule.span K ((s • Λ : Submodule (𝓞 K) V) : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := s.surjective x
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hL.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (apply_mem_smul s hy)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem (ha trivial) (hb trivial)
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c (ha trivial)
  refine ⟨(isLatMod_top_bot_iff _).2 ⟨Submodule.FG.map _ hL.fg, hspan⟩, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := s.surjective x
  rw [apply_mem_smul_iff, mem_dual_iff, hspan]
  conv_rhs => rw [← h2, mem_dual_iff, hL.span_eq_top]
  refine and_congr (by simp) ⟨fun hh x hx => ?_, fun hh x hx => ?_⟩
  · rw [← h]; exact hh _ (apply_mem_smul s hx)
  · obtain ⟨z, hz, rfl⟩ := exists_of_mem_smul hx
    rw [h]; exact hh z hz

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem sub_mem_left {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) {y : V}
    (hy : y ∈ uPerp F F') : s y - y ∈ F.X :=
  h.mid y fun x hx => (mem_perp_iff H _ y).1 hy x (Submodule.mem_sup_left hx)

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem sub_mem_right {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F' s) {y : V}
    (hy : y ∈ uPerp F F') : s y - y ∈ F'.X :=
  h.mid y fun x hx => (mem_perp_iff H _ y).1 hy x (Submodule.mem_sup_right hx)

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem shift (s : V ≃ₗ[K] V) {l x y : V} (h : l + x = y) : s l + (s x - (s y - y)) = y := by
  rw [← h, map_add]; abel

theorem latL_le {F : FlagD H r} (F' : FlagD H r) {s : V ≃ₗ[K] V} (h : Keeps F s)
    (Λ : Submodule (𝓞 K) V) : latL F F' Λ ≤ latL F F' (s • Λ) := by
  rintro y ⟨hy, hy'⟩
  obtain ⟨l, hl, x, hx, he⟩ := Submodule.mem_sup.1 hy'
  exact ⟨hy, Submodule.mem_sup.2 ⟨s l, apply_mem_smul s hl, _,
    sub_mem ((h.flagX _).2 hx) (sub_mem_left h hy), shift s he⟩⟩

theorem latL_eq {F : FlagD H r} (F' : FlagD H r) {s : V ≃ₗ[K] V} (h : Keeps F s)
    (Λ : Submodule (𝓞 K) V) : latL F F' (s • Λ) = latL F F' Λ := by
  refine le_antisymm ?_ (latL_le F' h Λ)
  simpa using latL_le F' h.inv (s • Λ)

theorem iotaGraph_le {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) (g : 𝓞 K) : iotaGraph F F' Λ g ≤ iotaGraph F F' (s • Λ) g := by
  rintro ⟨y', y⟩ ⟨⟨hy', hy⟩, hp⟩
  obtain ⟨⟨l', l⟩, ⟨⟨hl', hl⟩, hc⟩, ⟨x', x⟩, ⟨hx', hx⟩, he⟩ := Submodule.mem_sup.1 hp
  have he1 : l' + x' = y' := congrArg Prod.fst he
  have he2 : l + x = y := congrArg Prod.snd he
  refine ⟨⟨⟨latL_le F h' Λ hy'.1, hy'.2⟩, ⟨latL_le F' h Λ hy.1, hy.2⟩⟩, ?_⟩
  refine Submodule.mem_sup.2 ⟨(s l', s l), ⟨⟨apply_mem_smul s hl', apply_mem_smul s hl⟩, ?_⟩,
    (s x' - (s y' - y'), s x - (s y - y)),
    ⟨sub_mem ((h'.flagX _).2 hx') (sub_mem_left h' hy'.1.1),
      sub_mem ((h.flagX _).2 hx) (sub_mem_left h hy.1.1)⟩,
    Prod.ext (shift s he1) (shift s he2)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hc
  have hab' : a + b = l - l' := hab
  refine Submodule.mem_sup.2 ⟨s a, apply_mem_smulLat s g ha, s b,
    ⟨apply_mem_smul s hb.1, (h.flagX _).2 hb.2⟩, ?_⟩
  show _ = s l - s l'
  rw [← map_add, hab', map_sub]

theorem iotaGraph_eq {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) (g : 𝓞 K) : iotaGraph F F' (s • Λ) g = iotaGraph F F' Λ g := by
  refine le_antisymm ?_ (iotaGraph_le h h' Λ g)
  simpa using iotaGraph_le h.inv h'.inv (s • Λ) g

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem apply_mem_II {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s) (x : V) :
    s x ∈ II F F' ↔ x ∈ II F F' :=
  and_congr (h.flagX x) (h'.flagX x)

theorem latTh_le {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) : latTh F F' Λ ≤ latTh F F' (s • Λ) := by
  rintro y ⟨⟨hy1, hy2⟩, hy3⟩
  obtain ⟨l, ⟨hl, hl'⟩, x, hx, he⟩ := Submodule.mem_sup.1 hy1
  refine ⟨⟨Submodule.mem_sup.2 ⟨s l, ⟨apply_mem_smul s hl, ?_⟩, _,
    sub_mem ((apply_mem_II h h' _).2 hx) ⟨sub_mem_left h hy2, sub_mem_right h' hy2⟩,
    shift s he⟩, hy2⟩, hy3⟩
  refine (mem_perp_iff H _ _).2 fun z hz => ?_
  obtain ⟨w, rfl⟩ := s.surjective z
  rw [h.iso]
  exact (mem_perp_iff H _ _).1 hl' w ((apply_mem_II h h' _).1 hz)

theorem latTh_eq {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) : latTh F F' (s • Λ) = latTh F F' Λ := by
  refine le_antisymm ?_ (latTh_le h h' Λ)
  simpa using latTh_le h.inv h'.inv (s • Λ)

omit [StarRing K] in
theorem smul_inf_rs (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) {S : Submodule K V}
    (hS : ∀ x, s x ∈ S ↔ x ∈ S) : s • Λ ⊓ rs (𝓞 K) S = s • (Λ ⊓ rs (𝓞 K) S) := by
  ext x
  obtain ⟨y, rfl⟩ := s.surjective x
  rw [apply_mem_smul_iff, Submodule.mem_inf, Submodule.mem_inf, apply_mem_smul_iff]
  exact and_congr Iff.rfl (hS y)

omit [StarRing K] in
theorem idx_smul (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) : idx (s • A) (s • B) = idx A B :=
  AddSubgroup.relIndex_map_map_of_injective B.toAddSubgroup A.toAddSubgroup
    (f := s.toLinearMap.toAddMonoidHom) s.injective

theorem bOne_eq {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) (j : ℕ) : bOne F F' (s • Λ) j = bOne F F' Λ j := by
  unfold bOne latF
  rw [smul_inf_rs s Λ h.flagX, smul_inf_rs s Λ (h.flag j), smul_inf_rs s Λ (apply_mem_II h h'),
    ← Submodule.smul_sup', idx_smul]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ s ∈ N.R, N.IsTerm g (s • Λ) ∧ N.SameDat g Λ (s • Λ) ∧ latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ ∧ N.bI (s • Λ) = N.bI Λ := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hΛ s hs
  obtain ⟨h, h'⟩ := keeps_of_mem N hs
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hΛ
  exact ⟨⟨⟨isUnimod_smul h.iso h1, isFrame_smul h h2, isFrame_smul h' h3⟩, isAdm_smul h h' h4⟩,
    ⟨latL_eq _ h Λ, latL_eq _ h' Λ, iotaGraph_eq h h' Λ _⟩, latTh_eq h h' Λ, bOne_eq h h' Λ _⟩

end GlobalTheory.DegCnt.StabInv
