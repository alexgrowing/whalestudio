import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.DelScale

open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder

section General

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem idx_eq (A B : Submodule R W) : idx A B = idxN A B := rfl

theorem idx_inf_left (A B : Submodule R W) : idx A (A ⊓ B) = idx A B :=
  AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup

theorem idx_inf_right (A B : Submodule R W) : idx B (A ⊓ B) = idx B A :=
  AddSubgroup.inf_relIndex_right A.toAddSubgroup B.toAddSubgroup

theorem idx_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) : idx B A * idx C B = idx C A :=
  idxN_mul h1 h2

theorem gidx_of_le {A B N : Submodule R W} (h1 : N ≤ A) (h2 : N ≤ B) (hA : idx A N ≠ 0) :
    gidx A B = (idx A N : ℝ) / idx B N := by
  have a := idx_mul (le_inf h1 h2) (inf_le_left : A ⊓ B ≤ A)
  have b := idx_mul (le_inf h1 h2) (inf_le_right : A ⊓ B ≤ B)
  rw [idx_inf_left] at a
  rw [idx_inf_right] at b
  have h0 : idx (A ⊓ B) N ≠ 0 := fun e => hA (by rw [← a, e, zero_mul])
  rw [gidx, ← a, ← b]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]

theorem gidx_of_ge {A B L : Submodule R W} (h1 : A ≤ L) (h2 : B ≤ L) (hA : idx L A ≠ 0)
    (hB : idx B A ≠ 0) : gidx A B = (idx L B : ℝ) / idx L A := by
  have a := idx_mul (inf_le_left : A ⊓ B ≤ A) h1
  have b := idx_mul (inf_le_right : A ⊓ B ≤ B) h2
  rw [idx_inf_left] at a
  rw [idx_inf_right, ← a] at b
  rw [gidx, div_eq_div_iff (by exact_mod_cast hB) (by exact_mod_cast hA)]
  rw [mul_comm (idx L B : ℝ)]
  exact_mod_cast b.symm

theorem idx_sup {X B I : Submodule R W} (h : I ≤ B) : idx (X ⊔ I) B = idx X B := by
  have e : X ⊔ I = X ⊔ ((X ⊔ I) ⊓ B) :=
    le_antisymm (sup_le le_sup_left (le_sup_of_le_right (le_inf le_sup_right h)))
      (sup_le le_sup_left inf_le_left)
  rw [← idx_inf_left]
  set T := (X ⊔ I) ⊓ B with hT
  have e2 : X ⊓ T = X ⊓ B := by rw [hT, ← inf_assoc, inf_sup_self]
  rw [e, ← idx_inf_left X B, ← e2, idx_inf_left]
  unfold idx
  rw [Submodule.sup_toAddSubgroup]
  exact AddSubgroup.relIndex_sup_right _ _

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

section Nondeg

omit [StarRing K] [FiniteDimensional K V] in
theorem gidx_pos {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    0 < gidx A B :=
  div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (idxN_ne_zero hB hA.fg)))
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (idxN_ne_zero hA hB.fg)))

omit [StarRing K] [FiniteDimensional K V] in
theorem gidx_mul {A B C : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hC : Submodule.IsLattice K C) : gidx A B * gidx B C = gidx A C := by
  have hL : (A ⊔ B ⊔ C).FG := (hA.fg.sup hB.fg).sup hC.fg
  have a : A ≤ A ⊔ B ⊔ C := le_sup_of_le_left le_sup_left
  have b : B ≤ A ⊔ B ⊔ C := le_sup_of_le_left le_sup_right
  have c : C ≤ A ⊔ B ⊔ C := le_sup_right
  have a0 : idx (A ⊔ B ⊔ C) A ≠ 0 := idxN_ne_zero hA hL
  have b0 : idx (A ⊔ B ⊔ C) B ≠ 0 := idxN_ne_zero hB hL
  rw [gidx_of_ge a b a0 (idxN_ne_zero hA hB.fg), gidx_of_ge b c b0 (idxN_ne_zero hB hC.fg),
    gidx_of_ge a c a0 (idxN_ne_zero hA hC.fg)]
  have : (idx (A ⊔ B ⊔ C) B : ℝ) ≠ 0 := by exact_mod_cast b0
  have : (idx (A ⊔ B ⊔ C) A : ℝ) ≠ 0 := by exact_mod_cast a0
  field_simp

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem gidx_dual {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    gidx (Formalism.HermitianLatticesTheory.dual h A) (Formalism.HermitianLatticesTheory.dual h B) = gidx B A := by
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have an := (Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).1
  have hL : Submodule.IsLattice K (A ⊔ B) := Submodule.IsLattice.sup K A B
  rw [gidx_of_le (an _ _ (le_sup_left : A ≤ A ⊔ B)) (an _ _ (le_sup_right : B ≤ A ⊔ B))
      (idxN_ne_zero (dl _ hL).1 (dl _ hA).1.fg),
    gidx_of_ge (le_sup_right : B ≤ A ⊔ B) (le_sup_left : A ≤ A ⊔ B) (idxN_ne_zero hB hL.fg)
      (idxN_ne_zero hB hA.fg)]
  rw [idx_eq (Formalism.HermitianLatticesTheory.dual h A), idx_eq (Formalism.HermitianLatticesTheory.dual h B), idxN_dual h hs hn hA _ _ hL le_sup_left rfl,
    idxN_dual h hs hn hB _ _ hL le_sup_right rfl]
  rfl

theorem gidx_disc {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    gidx (Formalism.HermitianLatticesTheory.dual h B) B = gidx A B ^ 2 * gidx (Formalism.HermitianLatticesTheory.dual h A) A := by
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  rw [← gidx_mul (dl _ hB).1 (dl _ hA).1 hB, ← gidx_mul (dl _ hA).1 hA hB, gidx_dual h hs hn hB hA]
  ring

end Nondeg

section Compl

variable {S I C : Submodule K V} (p : V →ₗ[K] V) (hCS : C ≤ S) (hpC : ∀ x ∈ S, p x ∈ C)
  (hpI : ∀ x, x - p x ∈ I) (hI : ∀ x ∈ I, p x = 0) (hC : ∀ x ∈ C, p x = x)

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
include hpC hpI in
theorem idx_latIn {A B : Submodule (𝓞 K) V} (hA : rs (𝓞 K) I ≤ A) (hAS : A ≤ rs (𝓞 K) S)
    (hB : rs (𝓞 K) I ≤ B) : idx (latIn C A) (latIn C B) = idx A B := by
  have e : A = (A ⊓ rs (𝓞 K) C) ⊔ rs (𝓞 K) I := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hA)
    have h1 : x - p x ∈ A := hA (hpI x)
    have h2 : p x ∈ A := by simpa using A.sub_mem hx h1
    have : x = p x + (x - p x) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨h2, hpC x (hAS hx)⟩ (hpI x)
  have e2 : idx A B = idx (A ⊓ rs (𝓞 K) C) B := by
    conv_lhs => rw [e]
    exact idx_sup hB
  rw [e2]
  have := AddSubgroup.relIndex_comap B.toAddSubgroup C.subtype.toAddMonoidHom (latIn C A).toAddSubgroup
  refine this.trans ?_
  unfold idx
  congr 1
  ext x
  simp only [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2⟩, h1, rfl⟩

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
theorem le_of_latMod {M : Submodule (𝓞 K) V} (hM : IsLatMod M S I) :
    rs (𝓞 K) I ≤ M ∧ M ≤ rs (𝓞 K) S := by
  obtain ⟨⟨N, -, hN⟩, hs⟩ := hM
  exact ⟨hN ▸ le_sup_right, fun x hx => hs ▸ Submodule.subset_span hx⟩

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
include hCS hpC hpI hI hC in
theorem latIn_isLattice {M : Submodule (𝓞 K) V} (hM : IsLatMod M S I) :
    Submodule.IsLattice K (latIn C M) := by
  obtain ⟨h1, h2⟩ := le_of_latMod hM
  obtain ⟨⟨N, hfg, hN⟩, hs⟩ := hM
  have hp : ∀ x ∈ M, p x ∈ M := fun x hx => by simpa using M.sub_mem hx (h1 (hpI x))
  constructor
  · apply Submodule.fg_of_fg_map_injective (C.subtype.restrictScalars (𝓞 K)) C.injective_subtype
    have : (latIn C M).map (C.subtype.restrictScalars (𝓞 K)) = N.map (p.restrictScalars (𝓞 K)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : V) ∈ N ⊔ rs (𝓞 K) I := hN ▸ hy
        obtain ⟨n, hn, i, hi, e⟩ := Submodule.mem_sup.1 hy'
        refine ⟨n, hn, ?_⟩
        change p n = y
        rw [← hC y y.2, ← e, map_add, hI i hi, add_zero]
      · rintro ⟨n, hn, rfl⟩
        have hn' : n ∈ M := hN ▸ Submodule.mem_sup_left hn
        exact ⟨⟨p n, hpC n (h2 hn')⟩, hp n hn', rfl⟩
    rw [this]
    exact hfg.map _
  · have key : ∀ x ∈ Submodule.span K (M : Set V),
        p x ∈ (Submodule.span K (latIn C M : Set C)).map C.subtype := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact ⟨⟨p x, hpC x (h2 hx)⟩, Submodule.subset_span (hp x hx), rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ a b => rw [map_add]; exact add_mem a b
      | smul r x _ a => rw [map_smul]; exact Submodule.smul_mem _ _ a
    rw [eq_top_iff]
    intro c _
    obtain ⟨y, hy, e⟩ := key c (hs ▸ hCS c.2)
    rw [hC c c.2] at e
    rwa [← Subtype.ext (show (y : V) = c from e)]

end Compl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (M M' : Submodule (𝓞 K) V) (S I : Submodule K V), I ≤ S → (∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) → IsLatMod M S I → IsLatMod M' S I → 0 < del H M ∧ 0 < gidx M M' ∧ del H M' = gidx M M' * del H M ∧ (IsIntegralLat H M → 1 ≤ del H M ∧ del H M ^ 2 = idx (dual H M) M) := by
  intro K V _ _ _ _ _ _ _ _ H _ M M' S I hIS hrad hM hM'
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective I.subtype (Submodule.ker_subtype I)
  have hr' : ∀ x (hx : x ∈ I), (r x : V) = x := fun x hx =>
    congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  set p : V →ₗ[K] V := LinearMap.id - I.subtype ∘ₗ r with hp
  have hpx : ∀ x, p x = x - r x := fun x => rfl
  set C : Submodule K V := S ⊓ LinearMap.ker r with hCd
  have hCS : C ≤ S := inf_le_left
  have hpC : ∀ x ∈ S, p x ∈ C := fun x hx => ⟨S.sub_mem hx (hIS (r x).2), by
    change r (p x) = 0
    rw [hpx, map_sub, sub_eq_zero]
    exact (Subtype.ext (hr' _ (r x).2)).symm⟩
  have hpI : ∀ x, x - p x ∈ I := fun x => by rw [hpx]; simp
  have hI : ∀ x ∈ I, p x = 0 := fun x hx => by rw [hpx, hr' x hx, sub_self]
  have hC : ∀ x ∈ C, p x = x := fun x hx => by
    have : r x = 0 := hx.2
    rw [hpx, this]; simp
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have o3 : ∀ y ∈ S, ∀ x, H.B y (p x) = H.B y x := fun y hy x => by
    rw [hpx, map_sub, o2 _ (r x).2 y hy, sub_zero]
  set h := hRes H.B.flip C with hh
  have hha : ∀ x y : C, h x y = H.B y x := fun _ _ => rfl
  have hs : h.IsSymm := ⟨fun x y => H.herm y x⟩
  have n0 : ∀ x : C, (∀ y : C, H.B x y = 0) → x = 0 := fun x hx => by
    have : (x : V) ∈ I := (hrad x (hCS x.2)).1 fun y hy => by
      rw [← o3 x (hCS x.2)]; exact hx ⟨_, hpC y hy⟩
    exact Subtype.ext ((hC x x.2).symm.trans (hI x this))
  have hn : h.Nondegenerate := ⟨fun x hx => n0 x fun y => by
    rw [← H.herm, ← hha, hx y, star_zero], fun x hx => n0 x fun y => hx y⟩
  have hd : ∀ {N : Submodule (𝓞 K) V}, IsLatMod N S I → rs (𝓞 K) I ≤ dual H N ∧ dual H N ≤ rs (𝓞 K) S ∧
      latIn C (dual H N) = Formalism.HermitianLatticesTheory.dual h (latIn C N) := by
    intro N hN
    obtain ⟨a, b⟩ := le_of_latMod hN
    refine ⟨fun i hi => ?_, fun y hy => ?_, ?_⟩
    · rw [mem_dual_iff, hN.2]
      exact ⟨hIS hi, fun x hx => by rw [o1 i hi x (b hx)]; exact zero_mem _⟩
    · rw [mem_dual_iff, hN.2] at hy
      exact hy.1
    · ext y
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      change (y : V) ∈ dual H N ↔ _
      rw [mem_dual_iff, hN.2]
      refine ⟨fun hy x hx => hy.2 x hx, fun hy => ⟨hCS y.2, fun x hx => ?_⟩⟩
      rw [← o3 y (hCS y.2)]
      exact hy ⟨p x, hpC x (b hx)⟩ (show p x ∈ N by simpa using N.sub_mem hx (a (hpI x)))
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K C h hs hn Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨a, b⟩ := le_of_latMod hM
  obtain ⟨a', b'⟩ := le_of_latMod hM'
  obtain ⟨d1, d2, d3⟩ := hd hM
  obtain ⟨d1', d2', d3'⟩ := hd hM'
  have L := latIn_isLattice p hCS hpC hpI hI hC hM
  have L' := latIn_isLattice p hCS hpC hpI hI hC hM'
  have g : ∀ {A B : Submodule (𝓞 K) V}, rs (𝓞 K) I ≤ A → A ≤ rs (𝓞 K) S → rs (𝓞 K) I ≤ B → B ≤ rs (𝓞 K) S →
      gidx A B = gidx (latIn C A) (latIn C B) := fun h1 h2 h3 h4 => by
    rw [gidx, gidx, idx_latIn p hpC hpI h1 h2 h3, idx_latIn p hpC hpI h3 h4 h1]
  have p1 : 0 < gidx (dual H M) M := by
    rw [g d1 d2 a b, d3]; exact gidx_pos (dl _ L).1 L
  have p2 : 0 < gidx M M' := by rw [g a b a' b']; exact gidx_pos L L'
  have p3 : gidx (dual H M') M' = gidx M M' ^ 2 * gidx (dual H M) M := by
    rw [g d1 d2 a b, g d1' d2' a' b', g a b a' b', d3, d3']
    exact gidx_disc h hs hn L L'
  refine ⟨Real.sqrt_pos.2 p1, p2, ?_, fun hi => ?_⟩
  · rw [del, del, p3, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq p2.le]
  · have hle : M ≤ dual H M := fun y hy => (mem_dual_iff H M y).2
      ⟨Submodule.subset_span hy, fun x hx => (isIntegralLat_iff H M).1 hi y hy x hx⟩
    have e : gidx (dual H M) M = idx (dual H M) M := by
      rw [gidx, idx_eq M, idxN_eq_one.2 hle]; simp
    refine ⟨?_, by rw [del, Real.sq_sqrt p1.le, e]⟩
    rw [e] at p1
    rw [del, e]
    exact Real.one_le_sqrt.2 (by exact_mod_cast p1)

end GlobalTheory.DegCnt.DelScale
