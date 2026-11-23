import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing

noncomputable section

set_option linter.unusedSectionVars false

open scoped Classical

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable (K) (H : Matrix ι ι E)

def hermPair (x y : ι → E) : E :=
  (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ y)

variable {K H}

theorem hermPair_add_right (x y z : ι → E) :
    hermPair K H x (y + z) = hermPair K H x y + hermPair K H x z := by
  simp [hermPair, mulVec_add, dotProduct_add]

theorem hermPair_smul_right (x y : ι → E) (c : E) :
    hermPair K H x (c • y) = c * hermPair K H x y := by
  simp [hermPair, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermPair_zero_right (x : ι → E) : hermPair K H x 0 = 0 := by
  simp [hermPair]

theorem hermPair_add_left (x y z : ι → E) :
    hermPair K H (x + y) z = hermPair K H x z + hermPair K H y z := by
  simp only [hermPair, Pi.add_apply, map_add]
  rw [show (fun i => conj K E (x i) + conj K E (y i)) =
    (fun i => conj K E (x i)) + (fun i => conj K E (y i)) from rfl, add_dotProduct]

theorem hermPair_smul_left (x y : ι → E) (c : E) :
    hermPair K H (c • x) y = conj K E c * hermPair K H x y := by
  simp only [hermPair, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => conj K E c * conj K E (x i)) = conj K E c • (fun i => conj K E (x i)) from
    rfl, smul_dotProduct, smul_eq_mul]

theorem hermPair_zero_left (y : ι → E) : hermPair K H 0 y = 0 := by
  simp [hermPair]

theorem hermPair_comm (hH : IsHermitianFor (conjHom K E) H) (x y : ι → E) :
    hermPair K H y x = conj K E (hermPair K H x y) := by
  have hHij : ∀ i j, H j i = conj K E (H i j) := fun i j => by
    have := congrFun (congrFun hH j) i
    simp only [transpose_apply, map_apply, conjHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    exact this.symm
  simp only [hermPair, dotProduct, mulVec, map_sum, map_mul, conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hHij]
  ring

theorem hermPair_eq_zero_comm (hH : IsHermitianFor (conjHom K E) H) {x y : ι → E} :
    hermPair K H y x = 0 ↔ hermPair K H x y = 0 := by
  rw [hermPair_comm hH]
  constructor
  · intro h
    have := congrArg (conj K E) h
    rwa [conj_conj, map_zero] at this
  · intro h
    rw [h, map_zero]

variable (K H)

def orth (W : Submodule E (ι → E)) : Submodule E (ι → E) where
  carrier := {y | ∀ x ∈ W, hermPair K H x y = 0}
  add_mem' {y z} hy hz x hx := by rw [hermPair_add_right, hy x hx, hz x hx, add_zero]
  zero_mem' x _ := hermPair_zero_right x
  smul_mem' c y hy x hx := by
    change hermPair K H x (c • y) = 0
    rw [hermPair_smul_right, hy x hx, mul_zero]

variable {K H}

theorem mem_orth {W : Submodule E (ι → E)} {y : ι → E} :
    y ∈ orth K H W ↔ ∀ x ∈ W, hermPair K H x y = 0 := Iff.rfl

theorem orth_antitone {W W' : Submodule E (ι → E)} (h : W ≤ W') : orth K H W' ≤ orth K H W :=
  fun _ hy x hx => hy x (h hx)

theorem orth_bot : orth K H (⊥ : Submodule E (ι → E)) = ⊤ := by
  ext y
  simp only [mem_orth, Submodule.mem_bot, forall_eq, Submodule.mem_top, iff_true]
  exact hermPair_zero_left y

variable (K H)

def IsTotallyIsotropic (W : Submodule E (ι → E)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, hermPair K H x y = 0

def IsAnisotropic : Prop :=
  ∀ x : ι → E, hermPair K H x x = 0 → x = 0

def wittIndex : ℕ :=
  sSup {d | ∃ W : Submodule E (ι → E), IsTotallyIsotropic K H W ∧ finrank E W = d}

variable {K H}

theorem IsTotallyIsotropic.le_orth {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    W ≤ orth K H W :=
  fun y hy x hx => hW x hx y hy

theorem isTotallyIsotropic_bot : IsTotallyIsotropic K H (⊥ : Submodule E (ι → E)) := by
  intro x hx y _
  rw [Submodule.mem_bot] at hx
  rw [hx]
  exact hermPair_zero_left y

theorem isTotallyIsotropic_span_singleton {x : ι → E} (hx : hermPair K H x x = 0) :
    IsTotallyIsotropic K H (E ∙ x) := by
  intro y hy z hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [hermPair_smul_left, hermPair_smul_right, hx, mul_zero, mul_zero]

theorem bddAbove_wittIndex_set :
    BddAbove {d | ∃ W : Submodule E (ι → E), IsTotallyIsotropic K H W ∧ finrank E W = d} := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro d ⟨W, -, rfl⟩
  calc finrank E W ≤ finrank E (ι → E) := Submodule.finrank_le W
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card E

theorem finrank_le_wittIndex {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    finrank E W ≤ wittIndex K H :=
  le_csSup bddAbove_wittIndex_set ⟨W, hW, rfl⟩

theorem anisotropic_iff_wittIndex_eq_zero : IsAnisotropic K H ↔ wittIndex K H = 0 := by
  constructor
  · intro h
    apply le_antisymm _ (Nat.zero_le _)
    refine csSup_le ⟨0, ⟨⊥, isTotallyIsotropic_bot, by simp⟩⟩ ?_
    rintro d ⟨W, hW, rfl⟩
    have : W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Submodule.mem_bot E).2 (h x (hW x hx x hx))
    subst this
    simp
  · intro h x hx
    by_contra hne
    have h1 := finrank_le_wittIndex (isTotallyIsotropic_span_singleton (K := K) (H := H) hx)
    rw [h, finrank_span_singleton hne] at h1
    exact absurd h1 (by norm_num)

end Form

section Flag

variable (K) (H : Matrix ι ι E)

structure IsotropicFlag where

  members : Finset (Submodule E (ι → E))

  isChain : IsChain (· ≤ ·) (members : Set (Submodule E (ι → E)))

  isotropic : ∀ W ∈ members, IsTotallyIsotropic K H W

variable {K H}

namespace IsotropicFlag

def IsProper (𝒲 : IsotropicFlag K H) : Prop := ∃ W ∈ 𝒲.members, W ≠ ⊥

def ofIsotropicVector {x : ι → E} (hx : hermPair K H x x = 0) : IsotropicFlag K H where
  members := {E ∙ x}
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    exact Or.inl le_rfl
  isotropic W hW := by
    rw [Finset.mem_singleton] at hW
    subst hW
    exact isTotallyIsotropic_span_singleton hx

theorem ofIsotropicVector_isProper {x : ι → E} (hx : hermPair K H x x = 0) (hx0 : x ≠ 0) :
    (ofIsotropicVector hx).IsProper :=
  ⟨E ∙ x, Finset.mem_singleton_self _, by
    rwa [Ne, Submodule.span_singleton_eq_bot]⟩

end IsotropicFlag

theorem not_isProper_of_isAnisotropic (h : IsAnisotropic K H) (𝒲 : IsotropicFlag K H) :
    ¬ 𝒲.IsProper := by
  rintro ⟨W, hW, hne⟩
  apply hne
  rw [eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot E).2 (h x (𝒲.isotropic W hW x hx x hx))

theorem exists_isProper_of_not_isAnisotropic (h : ¬ IsAnisotropic K H) :
    ∃ 𝒲 : IsotropicFlag K H, 𝒲.IsProper := by
  simp only [IsAnisotropic, not_forall] at h
  obtain ⟨x, hx, hx0⟩ := h
  exact ⟨_, IsotropicFlag.ofIsotropicVector_isProper hx hx0⟩

def fullChain (𝒲 : IsotropicFlag K H) : Finset (Submodule E (ι → E)) :=
  insert ⊥ (insert ⊤ (𝒲.members ∪ 𝒲.members.image (orth K H)))

theorem bot_mem_fullChain (𝒲 : IsotropicFlag K H) : ⊥ ∈ fullChain 𝒲 :=
  Finset.mem_insert_self _ _

theorem top_mem_fullChain (𝒲 : IsotropicFlag K H) : ⊤ ∈ fullChain 𝒲 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem mem_fullChain_of_mem {𝒲 : IsotropicFlag K H} {W : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) : W ∈ fullChain 𝒲 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hW))

theorem orth_mem_fullChain_of_mem {𝒲 : IsotropicFlag K H} {W : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) : orth K H W ∈ fullChain 𝒲 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hW)))

theorem le_orth_of_mem (𝒲 : IsotropicFlag K H) {W W' : Submodule E (ι → E)}
    (hW : W ∈ 𝒲.members) (hW' : W' ∈ 𝒲.members) : W ≤ orth K H W' := by
  rcases eq_or_ne W W' with rfl | hne
  · exact (𝒲.isotropic W hW).le_orth
  rcases 𝒲.isChain hW hW' hne with h | h
  · exact h.trans (𝒲.isotropic W' hW').le_orth
  · exact (𝒲.isotropic W hW).le_orth.trans (orth_antitone h)

theorem isChain_fullChain (𝒲 : IsotropicFlag K H) :
    IsChain (· ≤ ·) (fullChain 𝒲 : Set (Submodule E (ι → E))) := by
  have key : ∀ A ∈ fullChain 𝒲, ∀ B ∈ fullChain 𝒲, A ≤ B ∨ B ≤ A := by
    intro A hA B hB
    simp only [fullChain, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hA hB
    rcases hA with rfl | rfl | hA | ⟨W, hW, rfl⟩
    · exact Or.inl bot_le
    · exact Or.inr le_top
    · rcases hB with rfl | rfl | hB | ⟨W', hW', rfl⟩
      · exact Or.inr bot_le
      · exact Or.inl le_top
      · rcases eq_or_ne A B with rfl | hne
        · exact Or.inl le_rfl
        · exact 𝒲.isChain hA hB hne
      · exact Or.inl (le_orth_of_mem 𝒲 hA hW')
    · rcases hB with rfl | rfl | hB | ⟨W', hW', rfl⟩
      · exact Or.inr bot_le
      · exact Or.inl le_top
      · exact Or.inr (le_orth_of_mem 𝒲 hB hW)
      · rcases eq_or_ne W W' with rfl | hne
        · exact Or.inl le_rfl
        · rcases 𝒲.isChain hW hW' hne with h | h
          · exact Or.inr (orth_antitone h)
          · exact Or.inl (orth_antitone h)
  intro A hA B hB _
  exact key A hA B hB

def below (S : Finset (Submodule E (ι → E))) (B : Submodule E (ι → E)) :
    Submodule E (ι → E) :=
  (S.filter (· < B)).sup id

theorem below_le (S : Finset (Submodule E (ι → E))) (B : Submodule E (ι → E)) :
    below S B ≤ B := by
  apply Finset.sup_le
  intro A hA
  exact (Finset.mem_filter.1 hA).2.le

end Flag

section BaseChange

variable (K) (R : Type*) [CommRing R] [Algebra K R]

def toBase (x : ι → E) : ι → R ⊗[K] E :=
  fun i => Algebra.TensorProduct.includeRight (x i)

def extendScalars (W : Submodule E (ι → E)) : Submodule (R ⊗[K] E) (ι → R ⊗[K] E) :=
  Submodule.span (R ⊗[K] E) (toBase K R '' W)

variable {K R}

theorem toBase_mem_extendScalars {W : Submodule E (ι → E)} {x : ι → E} (hx : x ∈ W) :
    toBase K R x ∈ extendScalars K R W :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem extendScalars_mono {W W' : Submodule E (ι → E)} (h : W ≤ W') :
    extendScalars K R W ≤ extendScalars K R W' :=
  Submodule.span_mono (Set.image_mono h)

end BaseChange

section Groups

theorem unitaryMat_mul {H : Matrix ι ι E} {R : Type*} [CommRing R] [Algebra K R]
    (g h : unitaryPoints K E H R) : unitaryMat (g * h) = unitaryMat g * unitaryMat h := rfl

theorem unitaryMat_one {H : Matrix ι ι E} {R : Type*} [CommRing R] [Algebra K R] :
    unitaryMat (1 : unitaryPoints K E H R) = 1 := rfl

variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]

def parabolic (𝒲 : IsotropicFlag K H) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ W ∈ 𝒲.members, ∀ x ∈ extendScalars K R W,
    unitaryMat g *ᵥ x ∈ extendScalars K R W ∧ unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R W}
  one_mem' W _ x hx := by
    rw [inv_one, unitaryMat_one, one_mulVec]
    exact ⟨hx, hx⟩
  mul_mem' {g h} hg hh W hW x hx := by
    refine ⟨?_, ?_⟩
    · have : unitaryMat (g * h) *ᵥ x = unitaryMat g *ᵥ (unitaryMat h *ᵥ x) := by
        rw [unitaryMat_mul, ← mulVec_mulVec]
      rw [this]
      exact (hg W hW _ (hh W hW x hx).1).1
    · have : unitaryMat (g * h)⁻¹ *ᵥ x = unitaryMat h⁻¹ *ᵥ (unitaryMat g⁻¹ *ᵥ x) := by
        rw [_root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]
      rw [this]
      exact (hh W hW _ (hg W hW x hx).2).2
  inv_mem' {g} hg W hW x hx := by
    simp only [inv_inv]
    exact ⟨(hg W hW x hx).2, (hg W hW x hx).1⟩

variable {H R} in
theorem mem_parabolic {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ parabolic H R 𝒲 ↔ ∀ W ∈ 𝒲.members, ∀ x ∈ extendScalars K R W,
      unitaryMat g *ᵥ x ∈ extendScalars K R W ∧ unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R W :=
  Iff.rfl

def unipotentRadical (𝒲 : IsotropicFlag K H) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
    unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
    unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B)}
  one_mem' B _ x _ := by
    rw [inv_one, unitaryMat_one, one_mulVec, sub_self]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  mul_mem' {g h} hg hh B hB x hx := by
    have hbelow := extendScalars_mono (K := K) (R := R) (below_le (fullChain 𝒲) B)
    refine ⟨?_, ?_⟩
    · have hhx : unitaryMat h *ᵥ x ∈ extendScalars K R B := by
        have := hbelow (hh B hB x hx).1
        simpa using Submodule.add_mem _ this hx
      have : unitaryMat (g * h) *ᵥ x - x =
          (unitaryMat g *ᵥ (unitaryMat h *ᵥ x) - unitaryMat h *ᵥ x) +
            (unitaryMat h *ᵥ x - x) := by
        rw [unitaryMat_mul, ← mulVec_mulVec]; abel
      rw [this]
      exact Submodule.add_mem _ (hg B hB _ hhx).1 (hh B hB x hx).1
    · have hgx : unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R B := by
        have := hbelow (hg B hB x hx).2
        simpa using Submodule.add_mem _ this hx
      have : unitaryMat (g * h)⁻¹ *ᵥ x - x =
          (unitaryMat h⁻¹ *ᵥ (unitaryMat g⁻¹ *ᵥ x) - unitaryMat g⁻¹ *ᵥ x) +
            (unitaryMat g⁻¹ *ᵥ x - x) := by
        rw [_root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]; abel
      rw [this]
      exact Submodule.add_mem _ (hh B hB _ hgx).2 (hg B hB x hx).2
  inv_mem' {g} hg B hB x hx := by
    simp only [inv_inv]
    exact ⟨(hg B hB x hx).2, (hg B hB x hx).1⟩

variable {H R} in
theorem mem_unipotentRadical {𝒲 : IsotropicFlag K H} {g : unitaryPoints K E H R} :
    g ∈ unipotentRadical H R 𝒲 ↔ ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
      unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
      unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) :=
  Iff.rfl

theorem unipotentRadical_le_parabolic (𝒲 : IsotropicFlag K H) :
    unipotentRadical H R 𝒲 ≤ parabolic H R 𝒲 := by
  intro g hg W hW x hx
  have hB := mem_fullChain_of_mem hW
  have hbelow := extendScalars_mono (K := K) (R := R) (below_le (fullChain 𝒲) W)
  refine ⟨?_, ?_⟩
  · simpa using Submodule.add_mem _ (hbelow (hg W hB x hx).1) hx
  · simpa using Submodule.add_mem _ (hbelow (hg W hB x hx).2) hx

end Groups

section Rational

variable [NumberField K] (H : Matrix ι ι E)

def unipotentRational (𝒲 : IsotropicFlag K H) : Subgroup (unipotentRadical H 𝔸[K] 𝒲) :=
  (unitaryDiagonal K H).range.subgroupOf (unipotentRadical H 𝔸[K] 𝒲)

end Rational

end

end GroundTheory.Heights₂.Theta
