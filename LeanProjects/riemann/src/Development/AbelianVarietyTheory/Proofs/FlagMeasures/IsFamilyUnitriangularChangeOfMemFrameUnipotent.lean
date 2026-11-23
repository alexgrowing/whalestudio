import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.NFrameTri

section Gen

variable {K : Type} [CommRing K] {W : Type} [AddCommGroup W] [Module K W] {m : ℕ}

def flag (K : Type) [CommRing K] [Module K W] (f : Fin m → W) (j : ℕ) : Submodule K W :=
  Submodule.span K (f '' {a | a.val < j})

lemma flag_mono (f : Fin m → W) {i j : ℕ} (h : i ≤ j) : flag K f i ≤ flag K f j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

lemma flag_zero (f : Fin m → W) : flag K f 0 = ⊥ := by
  simp [flag]

def Lowers (f : Fin m → W) (n : W ≃ₗ[K] W) : Prop :=
  ∀ j, ∀ v ∈ flag K f (j + 1), n v - v ∈ flag K f j

lemma lowers_of_gen (f : Fin m → W) (n : W ≃ₗ[K] W)
    (h : ∀ b : Fin m, n (f b) - f b ∈ flag K f b.val) : Lowers f n := by
  intro j v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact flag_mono f (Nat.lt_succ_iff.mp hb) (h b)
  | zero => simp
  | add x y _ _ hx hy =>
    have : n (x + y) - (x + y) = (n x - x) + (n y - y) := by rw [map_add]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : n (c • x) - c • x = c • (n x - x) := by rw [map_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ c hx

lemma Lowers.mul {f : Fin m → W} {n n' : W ≃ₗ[K] W} (h : Lowers f n) (h' : Lowers f n') :
    Lowers f (n * n') := by
  intro j v hv
  have h1 := h' j v hv
  have h2 : n' v ∈ flag K f (j + 1) := by
    have : n' v = (n' v - v) + v := by abel
    rw [this]; exact add_mem (flag_mono f (Nat.le_succ j) h1) hv
  have : (n * n') v - v = (n (n' v) - n' v) + (n' v - v) := by
    rw [LinearEquiv.mul_apply]; abel
  rw [this]; exact add_mem (h j _ h2) h1

lemma Lowers.surj {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) :
    ∀ j, ∀ v ∈ flag K f j, ∃ w ∈ flag K f j, n w = v := by
  intro j
  induction j with
  | zero =>
    intro v hv
    rw [flag_zero, Submodule.mem_bot] at hv
    exact ⟨0, zero_mem _, by simp [hv]⟩
  | succ j ih =>
    intro v hv
    obtain ⟨w, hw, e⟩ := ih _ (h j v hv)
    refine ⟨v - w, sub_mem hv (flag_mono f (Nat.le_succ j) hw), ?_⟩
    rw [map_sub, e]; abel

lemma Lowers.inv {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Lowers f n⁻¹ := by
  intro j v hv
  obtain ⟨w, hw, rfl⟩ := h.surj _ v hv
  have e : n⁻¹ (n w) = w := n.symm_apply_apply w
  have : n⁻¹ (n w) - n w = -(n w - w) := by rw [e]; abel
  rw [this]; exact neg_mem (h j w hw)

lemma exists_coef (f : Fin m → W) (j : ℕ) (v : W) (hv : v ∈ flag K f j) :
    ∃ c : Fin m → K, (∀ a, j ≤ a.val → c a = 0) ∧ v = ∑ a, c a • f a := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨Pi.single b 1, fun a ha => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hb (not_lt.mpr ha)
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun a ha => by simp [hc a ha, hd a ha], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨s • c, fun a ha => by simp [hc a ha], by simp [Finset.smul_sum, smul_smul]⟩

lemma Lowers.tri {f : Fin m → W} {n : W ≃ₗ[K] W} (h : Lowers f n) : Tri K f (fun b => n (f b)) := by
  have : ∀ b : Fin m, ∃ c : Fin m → K, (∀ a, b.val ≤ a.val → c a = 0) ∧ n (f b) - f b = ∑ a, c a • f a :=
    fun b => exists_coef f _ _ (h b.val (f b) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩))
  choose c hc e using this
  refine ⟨Matrix.of fun a b => c b a + if a = b then 1 else 0, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
  · simp [hc b a hab.le, hab.ne']
  · simp [hc a a le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← e]
    simp

end Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma Fj_le_flag {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) (j : ℕ) : Fr.Fj j ≤ flag E Fr.f j := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.castSucc, ha, rfl⟩

lemma last_mem_perp {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) :
    Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
  intro x hx
  have : H.h x (Fr.f (Fin.last r)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  rw [H.h_herm, this, map_zero]

lemma lowers_of_mem_NSet {H : HermSp M V} {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.NSet) :
    Lowers Fr.f n := by
  obtain ⟨-, h1, h2⟩ := hn
  apply lowers_of_gen
  intro b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.span_mono ?_ (h2 _ (last_mem_perp Fr))
    rintro _ ⟨a, rfl⟩
    exact ⟨a.castSucc, a.isLt, rfl⟩
  | cast a =>
    exact Fj_le_flag Fr _ (h1 (a.val + 1) a.isLt (Fr.e a)
      (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩))

theorem tri_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) :
    ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  intro n hn
  apply Lowers.tri
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact lowers_of_mem_NSet Fr hx
  | one => intro j v _; simp
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

end GlobalTheory.NFrameTri
