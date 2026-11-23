import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEqv

section Count

variable {α : Type} {R : α → α → Prop}

theorem cntCl_eq_encard (hR : Equivalence R) (X : Set α) :
    cntCl X R = ((fun a => {b | R a b}) '' X).encard := by

  have hset : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} =
      (fun O => {b | b ∈ O ∧ b ∈ X}) '' ((fun a => {b | R a b}) '' X) := by
    ext O
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨{b | R a b}, ⟨a, ha, rfl⟩, by ext b; simp [and_comm]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by ext b; simp [and_comm]⟩
  rw [cntCl, hset]
  apply Set.InjOn.encard_image
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ hEq
  have hEq' : {b | b ∈ {b | R a b} ∧ b ∈ X} = {b | b ∈ {b | R a' b} ∧ b ∈ X} := hEq
  have hmem : a' ∈ {b | b ∈ {b | R a b} ∧ b ∈ X} := by
    rw [hEq']
    exact ⟨hR.refl a', ha'⟩
  have haa' : R a a' := hmem.1
  ext b
  exact ⟨fun hb => hR.trans (hR.symm haa') hb, fun hb => hR.trans haa' hb⟩

theorem encard_biUnion_le' {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    (⋃ i ∈ s, Y i).encard ≤ ∑ i ∈ s, (Y i).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

theorem cntCl_le_sum (hR : Equivalence R) {ι : Type} (s : Finset ι) (X : Set α) (Y : ι → Set α)
    (h : ∀ a ∈ X, ∃ i ∈ s, ∃ b ∈ Y i, R a b) : cntCl X R ≤ ∑ i ∈ s, cntCl (Y i) R := by
  simp only [cntCl_eq_encard hR]
  calc ((fun a => {b | R a b}) '' X).encard
      ≤ (⋃ i ∈ s, (fun a => {b | R a b}) '' Y i).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨i, hi, b, hb, hab⟩ := h a ha
        refine Set.mem_biUnion hi ⟨b, hb, ?_⟩
        ext c
        exact ⟨fun hc => hR.trans hab hc, fun hc => hR.trans (hR.symm hab) hc⟩
    _ ≤ ∑ i ∈ s, ((fun a => {b | R a b}) '' Y i).encard := encard_biUnion_le' s _

end Count

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

theorem mem_gmap (g : S.V ≃ₗ[E] S.V) (x : S.V) : x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

theorem aut_mem_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (x : S.V) : n x ∈ Λ ↔ x ∈ Λ := by
  have hx := mem_gmap (Λ := Λ) n (n x)
  rw [hn.2, LinearEquiv.symm_apply_apply] at hx
  exact hx

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

theorem X_le_orth : Xsp F ≤ orth S (Xsp F) := by

  have key : ∀ a, Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := fun a => by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.fl.e_iso a b
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have key2 : Xsp F ≤ LinearMap.ker (S.hT.flip y) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key a hy
  simpa using key2 hx

theorem symm_sub_mem (n : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) : ∀ x ∈ B, n.symm x - x ∈ A := by
  intro x hx

  have hmap : ∀ y ∈ B, n y ∈ B := fun y hy => by simpa using B.add_mem (hAB (h y hy)) hy
  have hinj : Function.Injective (n.toLinearMap.restrict hmap) := fun a b hab =>
    Subtype.ext (n.injective (congrArg Subtype.val hab))
  obtain ⟨⟨y, hy⟩, hyx⟩ := LinearMap.surjective_of_injective hinj ⟨x, hx⟩
  have hny : n y = x := congrArg Subtype.val hyx
  have hy' : n.symm x = y := by rw [← hny, LinearEquiv.symm_apply_apply]
  rw [hy', ← neg_sub]
  have hxy := h y hy
  rw [hny] at hxy
  exact A.neg_mem hxy

theorem trans_sub_mem (n m : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) (h' : ∀ x ∈ B, m x - x ∈ A) : ∀ x ∈ B, (m * n) x - x ∈ A := by
  intro x hx
  have hnx : n x ∈ B := by simpa using B.add_mem (hAB (h x hx)) hx
  show m (n x) - x ∈ A
  have e : m (n x) - x = (m (n x) - n x) + (n x - x) := by abel
  rw [e]
  exact A.add_mem (h' _ hnx) (h x hx)

theorem one_mem_NLam : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).one_mem, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · ext x
    rw [mem_gmap]
    rfl
  · simp
  · simp

theorem mul_mem_NLam {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : m * n ∈ NLam Λ F := by
  have hsymm : ∀ {k : S.V ≃ₗ[E] S.V}, IsAutLam S Λ k → ∀ y, k.symm y ∈ Λ ↔ y ∈ Λ := fun hk y => by
    rw [← aut_mem_iff hk, LinearEquiv.apply_symm_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hm.1.1 hn.1.1, ?_⟩,
    fun j => trans_sub_mem n m (Xflag_mono j) (hn.2.1 j) (hm.2.1 j),
    trans_sub_mem n m X_le_orth hn.2.2 hm.2.2⟩
  ext x
  rw [mem_gmap]
  exact (hsymm hn.1 _).trans (hsymm hm.1 _)

theorem symm_mem_NLam {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hn.1.1, ?_⟩,
    fun j => symm_sub_mem n (Xflag_mono j) (hn.2.1 j), symm_sub_mem n X_le_orth hn.2.2⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm]
  exact aut_mem_iff hn.1 x

theorem frameAct_one {k : ℕ} (f : Fin k → S.V) : frameAct f 1 = f := by
  funext b
  simp only [frameAct]
  rw [Finset.sum_eq_single b (fun a _ hab => by rw [Matrix.one_apply_ne hab]; simp)
    (fun hb => absurd (Finset.mem_univ b) hb), Matrix.one_apply_eq]
  simp

theorem frameAct_mul {k : ℕ} (f : Fin k → S.V) (ξ η : Matrix (Fin k) (Fin k) (𝓞 E)) :
    frameAct (frameAct f ξ) η = frameAct f (ξ * η) := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem map_frameAct {k : ℕ} (n : S.V ≃ₗ[E] S.V) (f : Fin k → S.V) (ξ : Matrix (Fin k) (Fin k) (𝓞 E)) :
    (fun a => n (frameAct f ξ a)) = frameAct (fun a => n (f a)) ξ := by
  funext b
  simp only [frameAct, map_sum, map_smul]

theorem uni_mul {k : ℕ} {O : Type} [CommRing O] {ξ η : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a b, b < a → η a b = 0) (a : Fin k) :
    (ξ * η) a a = ξ a a * η a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with hc | hc
    · rw [h1 a c hc, zero_mul]
    · rw [h2 c a hc, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem uni_inv {k : ℕ} {O : Type} [CommRing O] {ξ : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    ∃ η : Matrix (Fin k) (Fin k) O, (∀ a b, b < a → η a b = 0) ∧ (∀ a, η a a = 1) ∧ ξ * η = 1 := by

  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hu : IsUnit ξ.det := by
    rw [hdet]
    exact isUnit_one
  let _ := Matrix.invertibleOfIsUnitDet ξ hu
  have hinv : ξ⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ hu
  refine ⟨ξ⁻¹, fun a b hab => hinv hab, fun a => ?_, hmul⟩
  have hd := uni_mul h1 (fun a b hab => hinv hab) a
  rw [hmul, Matrix.one_apply_eq, h2, one_mul] at hd
  exact hd.symm

end Grp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TEqv_equivalence (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : Fg D T) :
    Equivalence (TEqv D Λ F (T' := T')) := by
  refine ⟨fun F' => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h h' => ?_⟩
  · refine ⟨1, one_mem_NLam, 1, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, ?_⟩
    rw [frameAct_one]
    rfl
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨η, hη1, hη2, hξη⟩ := uni_inv h1 h2
    refine ⟨n.symm, symm_mem_NLam hn, η, hη1, hη2, ?_⟩
    rw [hfr, map_frameAct]
    simp only [LinearEquiv.symm_apply_apply]
    rw [frameAct_mul, hξη, frameAct_one]
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨m, hm, ζ, k1, k2, hfr'⟩ := h'
    refine ⟨m * n, mul_mem_NLam hn hm, ξ * ζ, fun a b hab => ?_, fun a => ?_, ?_⟩
    · exact Matrix.BlockTriangular.mul (b := id) (fun i j hij => h1 i j hij) (fun i j hij => k1 i j hij) hab
    · rw [uni_mul h1 k1 a, h2, k2, one_mul]
    · rw [hfr', hfr, map_frameAct, frameAct_mul]
      rfl

end GlobalTheory.LoopC.FrEqv

end
