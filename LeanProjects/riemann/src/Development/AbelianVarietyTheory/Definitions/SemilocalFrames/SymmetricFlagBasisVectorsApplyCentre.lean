import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

@[simp] theorem ofHSpace_B {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (x y : S.V) : (ofHSpace S).B x y = S.hT y x := rfl

theorem isUnimod_ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (Λ : Submodule (NumberField.RingOfIntegers E) S.V) :
    IsUnimod (ofHSpace S) Λ ↔ Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ :=
  isUnimod_iff _ _

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def latU (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := latX F Λ ⊔ Submodule.span R {F.z}

def latUU (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := latU F Λ ⊔ latU F' Λ

def latSat (F F' : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R (V0 F F')

abbrev satQuot (F F' : FlagD H r) (Λ : Submodule R V) : Type :=
  ↥(latSat F F' Λ) ⧸ (latUU F F' Λ).submoduleOf (latSat F F' Λ)

def IsTransv (F F' : FlagD H r) : Prop :=
  Module.finrank K (V0 F F') = 2 * r + 2 ∧ Disjoint (V0 F F') (wSp F F')

def norLift (F F' : FlagD H r) : Submodule K V := V0 F F' ⊓ perp H (xPlus F)

def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X

def IsSig (F F' : FlagD H r) (y y' : V) (a a' : K) : Prop :=
  y ∈ norLift F F' ∧ y' ∈ norLift F' F ∧ IsComp F F' (y - y') a a'

def IsCong (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Prop :=
  latX F' Λ ⊔ smulLat g Λ = latX F Λ ⊔ smulLat g Λ ∧ F'.z - F.z ∈ latX F Λ ⊔ smulLat g Λ

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def redLat0 (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := redLat F Λ ⊓ rs R (perp H (xPlus F))

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ

def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add, add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2

theorem B_eq_zero_comm {x y : V} : H.B x y = 0 ↔ H.B y x = 0 :=
  ⟨fun h => by rw [← H.herm, h, star_zero], fun h => by rw [← H.herm, h, star_zero]⟩

theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)

theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]

theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]

theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp

theorem mem_perp_X (F : FlagD H r) (y : V) :
    y ∈ perp H F.X ↔ ∀ a : Fin r, H.B y (F.e a.castSucc) = 0 := by
  rw [X_eq_span, mem_perp_span, Set.forall_mem_range]

theorem X_le_perp (F : FlagD H r) : F.X ≤ perp H F.X := by
  intro x hx
  refine (mem_perp_X F x).2 fun a => B_eq_zero_comm.1 ?_
  exact (mem_perp_iff H _ _).1 ((mem_perp_X F _).2 fun b => F.iso a b) x hx

theorem z_mem_perp (F : FlagD H r) : F.z ∈ perp H F.X :=
  (mem_perp_X F _).2 fun a => B_eq_zero_comm.1 (F.zperp a)

theorem form_flag_vector_self (F : FlagD H r) : H.B F.z F.z = -F.T := F.zz

theorem X_le_xPlus (F : FlagD H r) : F.X ≤ xPlus F := le_sup_left

theorem z_mem_xPlus (F : FlagD H r) : F.z ∈ xPlus F :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]

theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp

theorem X_le_perp_xPlus (F : FlagD H r) : F.X ≤ perp H (xPlus F) := fun x hx =>
  (mem_perp_xPlus F x).2 ⟨X_le_perp F hx, B_eq_zero_comm.1 ((mem_perp_iff H _ _).1 (z_mem_perp F) x hx)⟩

theorem eq_zero_of_smul_z_mem (F : FlagD H r) {a : K} (h : a • F.z ∈ F.X) : a = 0 := by
  have h1 := ((mem_perp_xPlus F _).1 (X_le_perp_xPlus F h)).2
  rw [map_smul, LinearMap.smul_apply, form_flag_vector_self, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_right (neg_ne_zero.2 F.hT)

theorem B_congr (F : FlagD H r) {x x₁ y y₁ : V} (hx : x ∈ perp H F.X) (hy : y ∈ perp H F.X)
    (h1 : x₁ - x ∈ F.X) (h2 : y₁ - y ∈ F.X) : H.B x₁ y₁ = H.B x y := by
  have e1 : H.B x (y₁ - y) = 0 := (mem_perp_iff H _ _).1 hx _ h2
  have e2 : H.B (x₁ - x) y = 0 := B_eq_zero_comm.1 ((mem_perp_iff H _ _).1 hy _ h1)
  have e3 : H.B (x₁ - x) (y₁ - y) = 0 := (mem_perp_iff H _ _).1 (X_le_perp F h1) _ h2
  simp only [map_sub, LinearMap.sub_apply] at e1 e2 e3
  linear_combination e1 + e2 + e3

omit [IsScalarTower R K V] [Algebra R K] [StarRing K] [Field K] [Module K V] in

theorem mem_smulLat (g : R) (Λ : Submodule R V) (x : V) : x ∈ smulLat g Λ ↔ ∃ y ∈ Λ, g • y = x := by
  simp [smulLat]

theorem gL_eq_smulLat {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (g : ℕ) :
    gL Λ g = smulLat (g : NumberField.RingOfIntegers E) Λ := by
  ext x
  rw [mem_gL, mem_smulLat]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [int_smul_eq]
  rfl

omit [StarRing K] in

theorem mem_imLat (s : V ≃ₗ[K] V) (M : Submodule R V) (x : V) : x ∈ imLat s M ↔ ∃ y ∈ M, s y = x := Iff.rfl

theorem mem_latX (F : FlagD H r) (Λ : Submodule R V) (x : V) : x ∈ latX F Λ ↔ x ∈ Λ ∧ x ∈ F.X := Iff.rfl

theorem mem_redLat (F : FlagD H r) (Λ : Submodule R V) (x : V) :
    x ∈ redLat F Λ ↔ x ∈ perp H F.X ∧ ∃ a ∈ F.X, x + a ∈ Λ := by
  constructor
  · intro h
    obtain ⟨l, hl, a, ha, rfl⟩ := Submodule.mem_sup.1 h
    exact ⟨add_mem hl.2 (X_le_perp F ha), -a, neg_mem ha, by simpa using hl.1⟩
  · rintro ⟨h, a, ha, hl⟩
    exact Submodule.mem_sup.2 ⟨x + a, ⟨hl, add_mem h (X_le_perp F ha)⟩, -a, neg_mem ha, by simp⟩

theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]

theorem jointSpan_comm (F F' : FlagD H r) : V0 F' F = V0 F F' := by
  rw [← xPlus_sup, ← xPlus_sup, sup_comm]

theorem wSp_comm (F F' : FlagD H r) : wSp F' F = wSp F F' := by rw [wSp, wSp, jointSpan_comm]

theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]

theorem mem_norLift (F F' : FlagD H r) (y : V) :
    y ∈ norLift F F' ↔ y ∈ V0 F F' ∧ y ∈ perp H (xPlus F) := Iff.rfl

theorem X_le_norLift (F F' : FlagD H r) : F.X ≤ norLift F F' :=
  le_inf (le_sup_of_le_left le_sup_left) (X_le_perp_xPlus F)

theorem norLift_inf (F F' : FlagD H r) : norLift F F' ⊓ norLift F' F = V0 F F' ⊓ wSp F F' := by
  rw [norLift, norLift, wSp_eq, jointSpan_comm F F', inf_inf_inf_comm, inf_idem]

theorem IsTransv.symm {F F' : FlagD H r} (h : IsTransv F F') : IsTransv F' F := by
  rw [IsTransv, jointSpan_comm, wSp_comm]; exact h

theorem IsTransv.disjoint_norLift {F F' : FlagD H r} (h : IsTransv F F') :
    Disjoint (norLift F F') (norLift F' F) := by
  rw [disjoint_iff, norLift_inf]; exact h.2.eq_bot

theorem IsTransv.disjoint_xPlus {F F' : FlagD H r} (h : IsTransv F F') : Disjoint (xPlus F) (xPlus F') := by
  have hf : ∀ G : FlagD H r, Module.Finite K (xPlus G) := fun G => by
    rw [xPlus_eq_span]; exact Module.Finite.span_of_finite K (Set.finite_range _)
  have hd : ∀ G : FlagD H r, Module.finrank K (xPlus G) ≤ r + 1 := fun G => by
    rw [xPlus_eq_span]; exact (finrank_range_le_card (R := K) G.e).trans (by simp)
  have := hf F
  have := hf F'
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (xPlus F) (xPlus F')
  rw [xPlus_sup, h.1] at h1
  have h2 := hd F
  have h3 := hd F'
  have : Module.Finite K ↥(xPlus F ⊓ xPlus F') := Submodule.finiteDimensional_inf_left _ _
  rw [disjoint_iff, ← Submodule.finrank_eq_zero]
  omega

theorem isTransv_iff_gram (F F' : FlagD H r) : IsTransv F F' ↔ (Gram F F').det ≠ 0 := by
  classical
  have hV : V0 F F' = Submodule.span K (Set.range (Sum.elim F.e F'.e)) := by
    rw [Set.Sum.elim_range, Submodule.span_union, ← xPlus_eq_span, ← xPlus_eq_span, xPlus_sup]
  have hW : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → K,
      ∑ p, c p • Sum.elim F.e F'.e p ∈ wSp F F' ↔ Matrix.vecMul c (Gram F F') = 0 := fun c => by
    rw [wSp, hV, mem_perp_span, Set.forall_mem_range, funext_iff]
    refine forall_congr' fun q => ?_
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Gram, Matrix.of_apply,
      Pi.zero_apply]
  have hcard : Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 := by simp; omega
  have hli : LinearIndependent K (Sum.elim F.e F'.e) ↔ Module.finrank K (V0 F F') = 2 * r + 2 := by
    rw [linearIndependent_iff_card_eq_finrank_span, hV, hcard, eq_comm]; rfl
  rw [IsTransv, ← hli, Fintype.linearIndependent_iff, Ne, ← Matrix.exists_vecMul_eq_zero_iff,
    Submodule.disjoint_def]
  constructor
  · rintro ⟨h1, h2⟩ ⟨c, hc, h0⟩
    refine hc (funext (h1 c (h2 _ ?_ ((hW c).2 h0))))
    rw [hV]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · intro h
    have k : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → K, ∑ p, c p • Sum.elim F.e F'.e p ∈ wSp F F' → c = 0 :=
      fun c hc => by_contra fun hne => h ⟨c, hne, (hW c).1 hc⟩
    refine ⟨fun c hc => congrFun (k c (hc ▸ zero_mem _)), fun x hx hw => ?_⟩
    rw [hV] at hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    simp [k c hw]

theorem exists_isComp_iff (F F' : FlagD H r) (u : V) : (∃ a a', IsComp F F' u a a') ↔ u ∈ V0 F F' := by
  constructor
  · rintro ⟨a, a', h⟩
    exact Submodule.mem_sup.2 ⟨_, h, a • F.z + a' • F'.z, Submodule.mem_span_pair.2 ⟨a, a', rfl⟩, by abel⟩
  · intro h
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.1 hy
    refine ⟨a, a', ?_⟩
    unfold IsComp
    convert hx using 1
    abel

theorem isComp_iff (F F' : FlagD H r) (u : V) (a a' : K) :
    IsComp F F' u a a' ↔ ∃ ξ ∈ F.X, ∃ ξ' ∈ F'.X, u = ξ + a • F.z + ξ' + a' • F'.z := by
  rw [IsComp, Submodule.mem_sup]
  refine exists_congr fun ξ => and_congr_right fun _ => exists_congr fun ξ' => and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [add_right_comm ξ, h]; abel
  · rintro rfl; abel

theorem IsComp.swap {F F' : FlagD H r} {u : V} {a a' : K} (h : IsComp F F' u a a') : IsComp F' F u a' a := by
  rw [IsComp, sub_right_comm, sup_comm]; exact h

theorem isComp_zero_iff (F F' : FlagD H r) (u : V) : IsComp F F' u 0 0 ↔ u ∈ F.X ⊔ F'.X := by
  simp [IsComp]

theorem IsComp.add {F F' : FlagD H r} {u v : V} {a a' b b' : K} (h : IsComp F F' u a a')
    (k : IsComp F F' v b b') : IsComp F F' (u + v) (a + b) (a' + b') := by
  unfold IsComp at *
  convert add_mem h k using 1
  rw [add_smul, add_smul]; abel

theorem IsComp.smul {F F' : FlagD H r} {u : V} {a a' : K} (h : IsComp F F' u a a') (c : K) :
    IsComp F F' (c • u) (c * a) (c * a') := by
  unfold IsComp at *
  convert Submodule.smul_mem _ c h using 1
  rw [smul_sub, smul_sub, mul_smul, mul_smul]

theorem IsComp.sub {F F' : FlagD H r} {u v : V} {a a' b b' : K} (h : IsComp F F' u a a')
    (k : IsComp F F' v b b') : IsComp F F' (u - v) (a - b) (a' - b') := by
  simpa [sub_eq_add_neg] using h.add (k.smul (-1))

theorem IsComp.congr {F F' : FlagD H r} {u v : V} {a a' : K} (h : IsComp F F' u a a')
    (k : v - u ∈ F.X ⊔ F'.X) : IsComp F F' v a a' := by
  simpa using h.add ((isComp_zero_iff F F' _).2 k)

theorem IsComp.unique {F F' : FlagD H r} (hd : Disjoint (xPlus F) (xPlus F')) {u : V} {a a' b b' : K}
    (h : IsComp F F' u a a') (k : IsComp F F' u b b') : a = b ∧ a' = b' := by
  have key : ∀ {G G' : FlagD H r} {c c' : K}, Disjoint (xPlus G) (xPlus G') → IsComp G G' 0 c c' → c = 0 := by
    intro G G' c c' hG hc
    obtain ⟨ξ, hξ, ξ', hξ', e⟩ := (isComp_iff _ _ _ _ _).1 hc
    have h1 : ξ + c • G.z ∈ xPlus G := add_mem (X_le_xPlus G hξ) (Submodule.smul_mem _ c (z_mem_xPlus G))
    have h2 : ξ + c • G.z ∈ xPlus G' := by
      rw [add_assoc (ξ + c • G.z)] at e
      rw [eq_neg_of_add_eq_zero_left e.symm]
      exact neg_mem (add_mem (X_le_xPlus G' hξ') (Submodule.smul_mem _ c' (z_mem_xPlus G')))
    have h3 := Submodule.disjoint_def.1 hG _ h1 h2
    refine eq_zero_of_smul_z_mem G ?_
    rw [eq_neg_of_add_eq_zero_right h3]
    exact neg_mem hξ
  have h0 := h.sub k
  rw [sub_self] at h0
  exact ⟨sub_eq_zero.1 (key hd h0), sub_eq_zero.1 (key hd.symm h0.swap)⟩

theorem exists_isSig {F F' : FlagD H r} {y y' : V} (hy : y ∈ norLift F F') (hy' : y' ∈ norLift F' F) :
    ∃ a a', IsSig F F' y y' a a' := by
  obtain ⟨a, a', h⟩ := (exists_isComp_iff F F' (y - y')).2 (sub_mem hy.1 (jointSpan_comm F F' ▸ hy'.1))
  exact ⟨a, a', hy, hy', h⟩

theorem IsSig.congr {F F' : FlagD H r} {y y' y₁ y₁' : V} {a a' : K} (h : IsSig F F' y y' a a')
    (h1 : y₁ - y ∈ F.X) (h2 : y₁' - y' ∈ F'.X) : IsSig F F' y₁ y₁' a a' := by
  refine ⟨by simpa using add_mem (X_le_norLift F F' h1) h.1,
    by simpa using add_mem (X_le_norLift F' F h2) h.2.1, h.2.2.congr ?_⟩
  convert Submodule.add_mem_sup h1 (neg_mem h2) using 1
  abel

theorem IsSig.unique {F F' : FlagD H r} (hd : Disjoint (xPlus F) (xPlus F')) {y y' : V} {a a' b b' : K}
    (h : IsSig F F' y y' a a') (k : IsSig F F' y y' b b') : a = b ∧ a' = b' := h.2.2.unique hd k.2.2

theorem IsSig.add {F F' : FlagD H r} {y y' w w' : V} {a a' b b' : K} (h : IsSig F F' y y' a a')
    (k : IsSig F F' w w' b b') : IsSig F F' (y + w) (y' + w') (a + b) (a' + b') :=
  ⟨add_mem h.1 k.1, add_mem h.2.1 k.2.1, by rw [add_sub_add_comm]; exact h.2.2.add k.2.2⟩

theorem IsSig.smul {F F' : FlagD H r} {y y' : V} {a a' : K} (h : IsSig F F' y y' a a') (c : K) :
    IsSig F F' (c • y) (c • y') (c * a) (c * a') :=
  ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, by rw [← smul_sub]; exact h.2.2.smul c⟩

theorem IsSig.swap {F F' : FlagD H r} {y y' : V} {a a' : K} (h : IsSig F F' y y' a a') :
    IsSig F' F y' y (-a') (-a) :=
  ⟨h.2.1, h.1, by simpa using (h.2.2.smul (-1)).swap⟩

theorem IsCong.refl (F : FlagD H r) (Λ : Submodule R V) (g : R) : IsCong F F Λ g := ⟨rfl, by simp⟩

theorem IsCong.symm {F F' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g) : IsCong F' F Λ g :=
  ⟨h.1.symm, by rw [h.1, ← neg_sub]; exact neg_mem h.2⟩

theorem IsCong.trans {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g)
    (k : IsCong F' F'' Λ g) : IsCong F F'' Λ g :=
  ⟨k.1.trans h.1, by rw [← sub_add_sub_cancel _ F'.z]; exact add_mem (h.1.le k.2) h.2⟩

section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

theorem IsPairMap.mem_X_iff (h : IsPairMap F F' F'' Λ g β) (x : V) : β x ∈ F''.X ↔ x ∈ F'.X := by
  rw [← h.1]; simp

theorem IsPairMap.mem_perp_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := by
  rw [← h.2.1]; simp

theorem IsPairMap.mem_redLat_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ := by
  rw [← h.2.2.2.1, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem isPairMap_of_mem_iff (h1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X)
    (h2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X)
    (h3 : ∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y)
    (h4 : ∀ x, β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ) (h5 : β F'.z - F''.z ∈ F''.X)
    (h6 : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
      l'' - l' ∈ latX F Λ ⊔ smulLat g Λ) : IsPairMap F F' F'' Λ g β := by
  have k : ∀ {S S' : Submodule K V}, (∀ x, β x ∈ S' ↔ x ∈ S) → S.map (β : V →ₗ[K] V) = S' := by
    intro S S' hS
    ext y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [hS]; simp
  refine ⟨k h1, k h2, h3, ?_, h5, h6⟩
  ext y
  obtain ⟨x, rfl⟩ := β.surjective y
  rw [h4, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem IsPairMap.symm (h : IsPairMap F F' F'' Λ g β) : IsPairMap F F'' F' Λ g β.symm := by
  refine isPairMap_of_mem_iff (fun x => by rw [← h.mem_X_iff]; simp) (fun x => by rw [← h.mem_perp_iff]; simp)
    (fun x hx y hy => ?_) (fun x => by rw [← h.mem_redLat_iff]; simp) ?_ fun l hl l' hl' e => ?_
  · rw [← h.2.2.1 _ (by rw [← h.mem_perp_iff]; simpa using hx) _ (by rw [← h.mem_perp_iff]; simpa using hy)]
    simp
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub]
    exact neg_mem h.2.2.2.2.1
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub, neg_mem_iff] at e
    rw [← neg_sub]
    exact neg_mem (h.2.2.2.2.2 l' hl' l hl e)

theorem IsPairMap.congr (h : IsPairMap F F' F'' Λ g β) {β₁ : V ≃ₗ[K] V}
    (h1 : F'.X.map (β₁ : V →ₗ[K] V) = F''.X) (h2 : (perp H F'.X).map (β₁ : V →ₗ[K] V) = perp H F''.X)
    (he : ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X) : IsPairMap F F' F'' Λ g β₁ := by
  have k2 : ∀ x, β₁ x ∈ perp H F''.X ↔ x ∈ perp H F'.X := fun x => by rw [← h2]; simp
  refine isPairMap_of_mem_iff (fun x => by rw [← h1]; simp) k2 (fun x hx y hy => ?_) (fun x => ?_) ?_
    fun l hl l' hl' e => h.2.2.2.2.2 l hl l' hl' ?_
  · rw [B_congr F'' ((h.mem_perp_iff x).2 hx) ((h.mem_perp_iff y).2 hy) (he x hx) (he y hy), h.2.2.1 x hx y hy]
  · have k : x ∈ perp H F'.X → (β₁ x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ) := fun hx => by
      have hm : β₁ x - β x ∈ redLat F'' Λ := Submodule.mem_sup_right (he x hx)
      rw [← h.mem_redLat_iff, ← Submodule.add_mem_iff_right _ hm (y := β x), sub_add_cancel]
    exact ⟨fun hx => (k ((k2 x).1 ((mem_redLat _ _ _).1 hx).1)).1 hx,
      fun hx => (k ((mem_redLat _ _ _).1 hx).1).2 hx⟩
  · simpa using add_mem (he _ (z_mem_perp F')) h.2.2.2.2.1
  · simpa using sub_mem e (he l hl.2)

theorem isPairMap_of_aut (hc : IsCong F F'' Λ g) (hβ : β ∈ isomGrp H) (hΛ : imLat β Λ = Λ)
    (hX : F'.X.map (β : V →ₗ[K] V) = F''.X) (hz : β F'.z - F''.z ∈ F''.X)
    (hι : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), β l' - l' ∈ latX F Λ ⊔ smulLat g Λ) :
    IsPairMap F F' F'' Λ g β := by
  have hB := (mem_isomGrp H β).1 hβ
  have k0 : ∀ x, β x ∈ Λ ↔ x ∈ Λ := fun x => by
    conv_lhs => rw [← hΛ, mem_imLat]
    exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have k1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X := fun x => by rw [← hX]; simp
  have k2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := fun x => by
    rw [mem_perp_iff, mem_perp_iff, β.surjective.forall]
    simp only [k1, hB]
  refine isPairMap_of_mem_iff k1 k2 (fun x _ y _ => hB x y) (fun x => ?_) hz fun l hl l' hl' e => ?_
  · rw [mem_redLat, mem_redLat, k2, β.surjective.exists]
    simp only [k1, ← map_add, k0]
  · have h1 : β l - l' ∈ latX F Λ ⊔ smulLat g Λ :=
      hc.1 ▸ Submodule.mem_sup_left ⟨sub_mem ((k0 l).2 hl.1) hl'.1, e⟩
    simpa using sub_mem (hι l hl) h1

theorem isPairMap_refl (hc : IsCong F F' Λ g) : IsPairMap F F' F' Λ g (LinearEquiv.refl K V) :=
  isPairMap_of_aut hc ((mem_isomGrp H _).2 fun _ _ => rfl) (by ext x; simp [mem_imLat]) (by simp) (by simp)
    (by simp)

theorem fixSp_le (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : fixSp F F' F'' β ≤ wSp F F' := fun _ h => h.1

theorem fixSp_congr {β₁ : V ≃ₗ[K] V} (he : ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X) :
    fixSp F F' F'' β₁ = fixSp F F' F'' β := by
  ext x
  refine and_congr_right fun hx => exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  have h1 := he x (perp_anti (S := F'.X) (S' := V0 F F') (le_sup_of_le_left le_sup_right) hx)
  rw [← Submodule.add_mem_iff_right _ h1 (y := β x - y), sub_add_sub_cancel]

theorem IsPairMap.fixSp_sup_X (h : IsPairMap F F' F'' Λ g β) :
    fixSp F F'' F' β.symm ⊔ F.X = fixSp F F' F'' β ⊔ F.X := by
  have key : ∀ {G G' : FlagD H r} {γ : V ≃ₗ[K] V}, IsPairMap F G G' Λ g γ →
      fixSp F G G' γ ⊔ F.X ≤ fixSp F G' G γ.symm ⊔ F.X := by
    intro G G' γ k
    refine sup_le ?_ le_sup_right
    rintro x ⟨hx, y, hy, h1, h2⟩
    refine Submodule.mem_sup.2 ⟨y, ⟨hy, x, hx, by rw [← neg_sub]; exact neg_mem h1, ?_⟩, x - y, h1, by simp⟩
    rw [← k.mem_X_iff, map_sub, γ.apply_symm_apply, ← neg_sub]
    exact neg_mem h2
  exact le_antisymm (key h.symm) (key h)

end Pair

namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

abbrev sp : HermSpace E (wittSpace E 2 1).V := ofHSpace (wittSpace E 2 1)

def vec (v : Fin 5 → ℤ) : (wittSpace E 2 1).V := (fun i => (v i : E) : Fin 5 → E)

def co (x : (wittSpace E 2 1).V) : Fin 5 → E := x

theorem sp_B (x y : (wittSpace E 2 1).V) : (sp E).B x y =
    -(star (co E y 0) * co E x 0) - star (co E y 1) * co E x 1 + star (co E y 2) * co E x 2 +
      star (co E y 3) * co E x 3 + star (co E y 4) * co E x 4 := by
  show ∑ i : Fin 5, star (co E y i) * sgn (wittSigns 2 1 i) * co E x i = _
  have h0 : wittSigns 2 1 (0 : Fin 5) = true := rfl
  have h1 : wittSigns 2 1 (1 : Fin 5) = true := rfl
  have h2 : wittSigns 2 1 (2 : Fin 5) = false := rfl
  have h3 : wittSigns 2 1 (3 : Fin 5) = false := rfl
  have h4 : wittSigns 2 1 (4 : Fin 5) = false := rfl
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]
  simp only [sgn, if_true, Bool.false_eq_true, if_false]
  ring

theorem sp_B_vec (v w : Fin 5 → ℤ) : (sp E).B (vec E v) (vec E w) =
    ((-(w 0 * v 0) - w 1 * v 1 + w 2 * v 2 + w 3 * v 3 + w 4 * v 4 : ℤ) : E) := by
  rw [sp_B]; simp [co, vec]

theorem mem_lat (x : (wittSpace E 2 1).V) :
    x ∈ (wittSpace E 2 1).L0 ↔ ∀ i, co E x i ∈ Set.range (algebraMap (𝓞 E) E) :=
  (Pi.basisFun E (Fin 5)).mem_span_iff_repr_mem (𝓞 E) (co E x)

theorem vec_mem (v : Fin 5 → ℤ) : vec E v ∈ (wittSpace E 2 1).L0 :=
  (mem_lat E _).2 fun i => ⟨v i, by simp [co, vec]⟩

def fl (m s : ℤ) (h1 : m * m = m) (h2 : s * s = m) : FlagD (sp E) 1 where
  e := ![vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m], vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m]]
  T := 1
  indep := by
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h (2 : Fin 5)
    have h0 : ((1 : ℤ) : E) = 0 := this
    simp at h0
  iso := by
    intro b c
    rw [Subsingleton.elim b 0, Subsingleton.elim c 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zperp := by
    intro b
    rw [Subsingleton.elim b 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zz := by
    refine (sp_B_vec E _ _).trans (Eq.trans (congrArg _ (?_ : _ = (-1 : ℤ))) (by simp))
    simp; linarith
  hT := one_ne_zero

abbrev flZero : FlagD (sp E) 1 := fl E 0 0 rfl rfl

abbrev flPos : FlagD (sp E) 1 := fl E 1 1 rfl rfl

abbrev flNeg : FlagD (sp E) 1 := fl E 1 (-1) rfl rfl

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

theorem fl_X : (fl E m s h1 h2).X = Submodule.span E {vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]} := by
  rw [X_eq_span, Set.range_unique]; rfl

theorem symmetricFlagBasisVectors_apply_centre : (fl E m s h1 h2).z = vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m] := rfl

theorem fl_z_mem : (fl E m s h1 h2).z ∈ (wittSpace E 2 1).L0 := vec_mem E _

theorem fl_latX : latX (fl E m s h1 h2) (wittSpace E 2 1).L0 =
    Submodule.span (𝓞 E) {vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]} := by
  ext x
  rw [mem_latX, fl_X, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hx, a, rfl⟩
    obtain ⟨c, hc⟩ := (mem_lat E _).1 hx 2
    have e : co E (a • vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]) 2 = a * ((1 : ℤ) : E) := rfl
    rw [e, Int.cast_one, mul_one] at hc
    exact ⟨c, by rw [← hc, algebraMap_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Submodule.smul_mem _ c (vec_mem E _), algebraMap _ E c, by rw [algebraMap_smul]⟩

theorem vec_sub_mem (v w u : Fin 5 → ℤ) (h : ∀ i, v i - w i = 2 * u i) :
    vec E v - vec E w ∈ smulLat ((2 : ℕ) : 𝓞 E) (wittSpace E 2 1).L0 := by
  rw [← gL_eq_smulLat, mem_gL]
  refine ⟨vec E u, vec_mem E u, funext fun i : Fin 5 => ?_⟩
  show ((2 : ℕ) : E) * (u i : E) = (v i : E) - (w i : E)
  exact_mod_cast (h i).symm

theorem isCong_fl : IsCong (flZero E) (fl E m s h1 h2) (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) := by
  have he := vec_sub_mem E ![1 + 2 * m, 0, 1, 2 * s, 2 * m] ![1 + 2 * 0, 0, 1, 2 * 0, 2 * 0] ![m, 0, 0, s, m]
    (fun i => by fin_cases i <;> simp)
  refine ⟨?_, Submodule.mem_sup_right (vec_sub_mem E _ _ ![0, m, 0, s, -m] fun i => by fin_cases i <;> simp)⟩
  rw [fl_latX, fl_latX]
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · exact Submodule.mem_sup.2 ⟨_, Submodule.mem_span_singleton_self _, _, he, add_sub_cancel _ _⟩
  · exact Submodule.mem_sup.2 ⟨_, Submodule.mem_span_singleton_self _, _, neg_mem he, by abel⟩

theorem gval_fl {s : ℤ} (h2 : s * s = 1) : Gval (flZero E) (fl E 1 s rfl h2) = 32 := by
  have hZ : Zhat (flZero E) (fl E 1 s rfl h2) = !![-2, 0; 0, -3] := by
    ext a b
    fin_cases a <;> fin_cases b <;> refine (sp_B_vec E _ _).trans ?_ <;> simp
  have d2 : Dl (flZero E) (fl E 1 s rfl h2) (1 + 1) le_rfl = 6 := by
    rw [Dl, hZ, Matrix.det_fin_two]; simp; norm_num
  have d1 : Dl (flZero E) (fl E 1 s rfl h2) 1 (Nat.le_succ 1) = -2 := by
    rw [Dl, hZ, Matrix.det_unique]; simp
  rw [Gval, d1, d2]
  show (6 : E) * star 6 - 1 * 1 * (-2 * star (-2)) = 32
  simp; norm_num

theorem isTransv_fl {s : ℤ} (h2 : s * s = 1) : IsTransv (flZero E) (fl E 1 s rfl h2) := by
  have h3 : (s : E) * s = 1 := by exact_mod_cast h2
  have hG : Gram (flZero E) (fl E 1 s rfl h2) =
      Matrix.fromBlocks !![0, 0; 0, -1] !![-2, 0; 0, -3] !![-2, 0; 0, -3] !![0, 0; 0, -1] := by
    ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;> refine (sp_B_vec E _ _).trans ?_ <;>
      simp <;> linear_combination 4 * h3
  rw [isTransv_iff_gram, hG, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  rintro ⟨c, hc, h⟩
  have a0 := congrFun h (Sum.inl 0)
  have a1 := congrFun h (Sum.inl 1)
  have b0 := congrFun h (Sum.inr 0)
  have b1 := congrFun h (Sum.inr 1)
  simp [Matrix.vecMul, dotProduct] at a0 a1 b0 b1
  have c1 : c (Sum.inr 1) = 0 := by linear_combination (1 / 8 : E) * b1 - (3 / 8 : E) * a1
  have c0 : c (Sum.inl 1) = 0 := by linear_combination (1 / 8 : E) * a1 - (3 / 8 : E) * b1
  refine hc (funext fun p => ?_)
  rcases p with p | p <;> fin_cases p <;> assumption

def flip : (wittSpace E 2 1).V ≃ₗ[E] (wittSpace E 2 1).V :=
  LinearEquiv.piCongrRight (R := E) (φ := fun _ : Fin 5 => E) (ψ := fun _ : Fin 5 => E)
    fun i => if i = 3 then LinearEquiv.neg E else LinearEquiv.refl E E

theorem co_flip (x : (wittSpace E 2 1).V) (i : Fin 5) :
    co E (flip E x) i = if i = 3 then -co E x i else co E x i := by
  show (if i = 3 then LinearEquiv.neg E else LinearEquiv.refl E E : E ≃ₗ[E] E) (co E x i) = _
  split_ifs <;> rfl

theorem flip_vec (a b c d e : ℤ) : flip E (vec E ![a, b, c, d, e]) = vec E ![a, b, c, -d, e] := by
  refine funext fun i : Fin 5 => (co_flip E _ i).trans ?_
  fin_cases i <;> simp [co, vec]

theorem isPairMap_flip :
    IsPairMap (flZero E) (flPos E) (flNeg E) (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) (flip E) := by
  have hL : ∀ x, flip E x ∈ (wittSpace E 2 1).L0 ↔ x ∈ (wittSpace E 2 1).L0 := fun x => by
    rw [mem_lat, mem_lat]
    refine forall_congr' fun i => ?_
    rw [co_flip]
    split_ifs
    · exact neg_mem_iff (H := (algebraMap (𝓞 E) E).range)
    · rfl
  refine isPairMap_of_aut (isCong_fl E _ _) ((mem_isomGrp _ _).2 fun x y => ?_) ?_ ?_ ?_ fun l hl => ?_
  · rw [sp_B, sp_B]; simp [co_flip]
  · ext y
    obtain ⟨x, rfl⟩ := (flip E).surjective y
    rw [mem_imLat]
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ (hL y).2 hy, fun hx => ⟨x, (hL x).1 hx, rfl⟩⟩
  · rw [fl_X, fl_X, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, flip_vec]; rfl
  · have e : flip E (flPos E).z = (flNeg E).z := flip_vec E _ _ _ _ _
    rw [e, sub_self]
    exact zero_mem _
  · refine Submodule.mem_sup_right ?_
    rw [← gL_eq_smulLat, mem_gL]
    refine ⟨(fun i => if i = 3 then -co E l i else 0 : Fin 5 → E), (mem_lat E _).2 fun i => ?_,
      funext fun i : Fin 5 => ?_⟩
    · show (if i = 3 then -co E l i else 0) ∈ (algebraMap (𝓞 E) E).range
      split_ifs
      · exact neg_mem ((mem_lat E l).1 hl.1 i)
      · exact zero_mem _
    · show ((2 : ℕ) : E) * (if i = 3 then -co E l i else 0) = co E (flip E l) i - co E l i
      rw [co_flip]
      split_ifs <;> push_cast <;> ring

theorem X_ne : (flPos E).X ≠ (flNeg E).X := by
  intro h
  have hm : vec E ![1 + 2 * 1, 0, 1, 2 * 1, 2 * 1] ∈ (flNeg E).X := by
    rw [← h, fl_X]; exact Submodule.mem_span_singleton_self _
  have h0 := (mem_perp_X (flNeg E) _).1 (X_le_perp _ hm) 0
  have h1 := (sp_B_vec E _ _).symm.trans h0
  simp at h1

theorem exists_pair : ∃ (F F' F'' : FlagD (ofHSpace (wittSpace E 2 1)) 1)
    (β : (wittSpace E 2 1).V ≃ₗ[E] (wittSpace E 2 1).V),
    IsUnimod (ofHSpace (wittSpace E 2 1)) (wittSpace E 2 1).L0 ∧
    F.z ∈ (wittSpace E 2 1).L0 ∧ F'.z ∈ (wittSpace E 2 1).L0 ∧ F''.z ∈ (wittSpace E 2 1).L0 ∧
    F.T = 1 ∧ F'.T = 1 ∧ F''.T = 1 ∧
    IsCong F F' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧ IsCong F F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧
    Gval F F' ≠ 0 ∧ Gval F F'' ≠ 0 ∧ IsTransv F F' ∧ IsTransv F F'' ∧ F'.X ≠ F''.X ∧
    IsPairMap F F' F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) β :=
  ⟨flZero E, flPos E, flNeg E, flip E,
    (isUnimod_ofHSpace _ _).2 ⟨(wittSpace E 2 1).standardTuple_isLattice, (wittSpace E 2 1).baseLattice_isUnimodular⟩,
    fl_z_mem E _ _, fl_z_mem E _ _, fl_z_mem E _ _, rfl, rfl, rfl, isCong_fl E _ _, isCong_fl E _ _,
    by rw [gval_fl]; norm_num, by rw [gval_fl]; norm_num, isTransv_fl E _, isTransv_fl E _, X_ne E,
    isPairMap_flip E⟩

example : ¬ IsPairMap (flZero E) (flPos E) (flNeg E) (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E)
    (LinearEquiv.refl E _) := fun h => X_ne E (by simpa using h.1)

example : vec E ![2, 0, 2, 1, 1] ∈ wSp (flZero E) (flPos E) ∧
    vec E ![2, 0, 2, 1, 1] ∉ fixSp (flZero E) (flPos E) (flNeg E) (flip E) := by
  constructor
  · rw [wSp_eq, Submodule.mem_inf, xPlus_eq_span, xPlus_eq_span, mem_perp_span, mem_perp_span,
      Set.forall_mem_range, Set.forall_mem_range]
    constructor <;> intro a <;> fin_cases a <;> refine (sp_B_vec E _ _).trans ?_ <;> simp
  · rintro ⟨-, y, hy, h, -⟩
    rw [fl_X, Submodule.mem_span_singleton] at h
    obtain ⟨t, ht⟩ := h
    rw [wSp_eq] at hy
    have h1 := ((mem_perp_xPlus _ _).1 hy.2).2
    rw [← sub_sub_cancel (vec E ![2, 0, 2, 1, 1]) y, ← ht, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, symmetricFlagBasisVectors_apply_centre, sp_B_vec, sp_B_vec] at h1
    simp at h1

example : IsComp (flZero E) (flPos E) ((flPos E).z - (flZero E).z) (-1) 1 := by simp [IsComp]

end FlagExample

end GlobalTheory.SA

end
