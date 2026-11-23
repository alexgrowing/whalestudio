import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestCone

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ v ∈ wtSub act μ ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

lemma Eab_mul (a b c d : Ix p q) :
    (Eab a b : Mat p q) * Eab c d = (if b = c then (1 : ℂ) else 0) • Eab a d := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne, h]

lemma lie_Eab {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b c d : Ix p q) (y : V) :
    act (Eab a b) (act (Eab c d) y) = act (Eab c d) (act (Eab a b) y) +
      ((if b = c then (1 : ℂ) else 0) • act (Eab a d) y -
        (if d = a then (1 : ℂ) else 0) • act (Eab c b) y) := by
  have := congrArg (fun f => f y) (hL (Eab a b) (Eab c d))
  simp only [Eab_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at this
  rw [this]; abel

lemma wt_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b : Ix p q)
    {ν : Ix p q → ℚ} {y : V} (hy : y ∈ wtSub act ν) :
    act (Eab a b) y ∈ wtSub act
      (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wt] at hy ⊢
  intro c
  rw [lie_Eab hL, hy, map_smul]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]
  · subst h2; simp [h1, sub_eq_add_neg, add_smul]
  · simp [h1, h2, Ne.symm h2]

def InCone (ν μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧
    μ = fun c => ν c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

lemma inCone_self (μ : Ix p q → ℚ) : InCone μ μ :=
  ⟨fun _ _ => 0, by simp, by simp⟩

lemma inCone_step {ν μ : Ix p q → ℚ} (h : InCone ν μ) (i : Fin p) (j : Fin q) :
    InCone (fun c => ν c + ((if c = Sum.inr j then 1 else 0) - (if c = Sum.inl i then 1 else 0))) μ := by
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨fun a b => m a b + if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0, ?_, ?_⟩
  · intro a b hab
    by_cases h0 : m a b = 0
    · by_cases h1 : a = Sum.inl i
      · by_cases h2 : b = Sum.inr j
        · exact ⟨i, j, h1, h2⟩
        · simp [h0, h2] at hab
      · simp [h0, h1] at hab
    · exact hm a b h0
  · funext c
    have key : ∑ a : Ix p q, ∑ b : Ix p q,
        (((if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0 : ℕ)) : ℚ) *
          ((if c = a then 1 else 0) - (if c = b then 1 else 0)) =
        (if c = Sum.inl i then 1 else 0) - (if c = Sum.inr j then 1 else 0) := by
      rw [Finset.sum_eq_single (Sum.inl i), Finset.sum_eq_single (Sum.inr j)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, key]
    ring

lemma act_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, act (Eab a b) y ∈ N) (Z : Mat p q) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b)

lemma exists_down {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) : ∃ D : Submodule ℂ V, v ∈ D ∧
      (∀ i j, ∀ x ∈ D, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ D) ∧
      (∀ a b, posC a b → ∀ x ∈ D, act (Eab a b) x ∈ D) ∧
      D ≤ ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1 := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ i j, ∀ x ∈ N, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b y (Submodule.mem_sInf.1 hy M hM)
  refine ⟨sInf S, hG.1, hG.2, fun a b hab x hx => ?_, sInf_le ⟨?_, fun i j x hx => ?_⟩⟩
  · have hG' : (sInf S ⊓ (sInf S).comap (act (Eab a b))) ∈ S := by
      refine ⟨⟨hG.1, ?_⟩, fun i j y hy => ⟨hG.2 i j y hy.1, ?_⟩⟩
      · show act (Eab a b) v ∈ sInf S
        rw [hv.2 a b hab]; exact Submodule.zero_mem _
      · show act (Eab a b) (act _ y) ∈ sInf S
        rw [lie_Eab hL]
        refine Submodule.add_mem _ (hG.2 i j _ hy.2) ?_
        rcases a with a | a <;> rcases b with b | b
        · refine Submodule.sub_mem _ (by simp) (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1))
        · exact absurd hab (by simp [posC])
        · exact absurd hab (by simp [posC])
        · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1)) (by simp)
    exact (sInf_le hG' hx).2
  · exact Submodule.mem_iSup_of_mem (⟨μ, inCone_self μ⟩ : {ν // InCone ν μ}) hv.1
  · refine Submodule.iSup_induction _ (motive := fun x => act (Eab (Sum.inr j) (Sum.inl i)) x ∈
      ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1) hx ?_ (by simp) ?_
    · intro ν y hy
      exact Submodule.mem_iSup_of_mem (⟨_, inCone_step ν.2 i j⟩ : {ν // InCone ν μ})
        (wt_shift hL _ _ hy)
    · intro y z hy hz
      rw [map_add]; exact Submodule.add_mem _ hy hz

lemma wt_orth {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H)
    (hadj : ∀ Z x y, inner ℂ (E (act Z x)) (E y) = inner ℂ (E x) (E (act (adjZ Z) y)))
    {ν Λ : Ix p q → ℚ} (hne : ν ≠ Λ) {x e : V} (hx : x ∈ wtSub act ν) (he : e ∈ wtSub act Λ) :
    inner ℂ (E x) (E e) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
  have h := hadj (Eab c c) x e
  rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, mem_wt.1 hx, mem_wt.1 he,
    map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast, ← sub_eq_zero,
    ← sub_mul] at h
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hc ?_
  exact_mod_cast sub_eq_zero.1 h0

theorem cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro p q M H _ _ E hE hadj Λ e he hlow hgen μ v hv
  by_contra hcone
  change ¬ InCone Λ μ at hcone
  obtain ⟨D, hvD, hDm, hDp, hDle⟩ := exists_down M.lie hv.2
  rw [mem_hw] at he
  let C : Submodule ℂ M.V := ((D.map E)ᗮ).comap E
  have hC : ∀ x, x ∈ C ↔ ∀ d ∈ D, inner ℂ (E d) (E x) = 0 := by
    intro x
    simp only [C, Submodule.mem_comap, Submodule.mem_orthogonal]
    constructor
    · intro h d hd; exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩; exact h d hd
  have hstab : ∀ a b, (∀ d ∈ D, M.act (Eab a b) d ∈ D) → ∀ x ∈ C, M.act (Eab b a) x ∈ C := by
    intro a b h x hx
    rw [hC] at hx ⊢
    intro d hd
    have := hadj (adjZ (Eab b a)) d x
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at this
    rw [← this, GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact hx _ (D.smul_mem _ (h d hd))
  have heC : e ∈ C := by
    rw [hC]
    intro d hd
    refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (E x) (E e) = 0) (hDle hd) ?_
      (by simp) ?_
    · intro ν y hy
      exact wt_orth E hadj (fun h : ν.1 = Λ => hcone (h ▸ ν.2)) hy he.1
    · intro y z hy hz
      rw [map_add, inner_add_left, hy, hz, add_zero]
  let r : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.1)
  have hr : Function.Injective r := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · congr 1; ext; omega
    · have := b.2; omega
    · have := a.2; omega
    · congr 1; ext; omega
  have hcase : ∀ a b, r a < r b → posC a b ∨ ∃ i j, a = Sum.inr j ∧ b = Sum.inl i := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · left; show a < b; rw [Fin.lt_def]; omega
    · have := b.2; omega
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · left; exact h
  obtain ⟨U, heU, hU, hUmin, -⟩ := GlobalTheory.ExtremalGen.exists_generated p q M.V M.act M.lie (fun _ _ => True)
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ r hr Λ e he.1 (by
      intro a b _ h
      rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
      · exact he.2 a b h
      · exact hlow i j)
  have hUC : U ≤ C := hUmin C heC (by
    intro a b _ h
    refine hstab a b ?_
    rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
    · exact hDp a b h
    · exact hDm i j)
  have hgU : genSub M.act {e} ≤ U :=
    sInf_le ⟨by simpa using heU, fun Z y hy => act_mem U y (fun a b => hU a b trivial y hy) Z⟩
  have hvC : v ∈ C := hUC (hgU (hgen ▸ Submodule.mem_top))
  have h0 := (hC v).1 hvC v hvD
  rw [inner_self_eq_zero] at h0
  exact hv.1 (hE (by rw [h0, map_zero]))

end GlobalTheory.LowestCone
