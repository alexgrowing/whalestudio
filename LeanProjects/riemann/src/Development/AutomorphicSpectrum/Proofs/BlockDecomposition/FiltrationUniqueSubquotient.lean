import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Filtration

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

noncomputable def descend (f : π.IntertwiningMap σ) (B A : Subrepresentation π)
    (h : ∀ v ∈ A.toSubmodule, f v = 0) : (subQuot B A).IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (f.toLinearMap ∘ₗ B.toSubmodule.subtype) (fun v hv => h v.1 hv)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact f.isIntertwining _ _ g v.1

theorem vanish_step (f : π.IntertwiningMap σ) {A B : Subrepresentation π}
    (hA : ∀ v ∈ A.toSubmodule, f v = 0)
    (hz : ∀ φ : (subQuot B A).IntertwiningMap σ, φ.toLinearMap = 0) :
    ∀ v ∈ B.toSubmodule, f v = 0 := by
  intro v hv
  have h1 := LinearMap.congr_fun (hz (GlobalTheory.CompanionTheory.Filtration.descend f B A hA)) (Submodule.Quotient.mk ⟨v, hv⟩)
  have h2 : (GlobalTheory.CompanionTheory.Filtration.descend f B A hA).toLinearMap (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rw [← h2, h1, LinearMap.zero_apply]

theorem vanish_climb {N : ℕ} (S : Fin (N + 1) → Subrepresentation π) (f : π.IntertwiningMap σ)
    (lo : ℕ) (hlo : lo < N + 1)
    (h0 : ∀ v ∈ (S ⟨lo, hlo⟩).toSubmodule, f v = 0) (hi : ℕ) (hle : lo ≤ hi) :
    ∀ (hhi : hi < N + 1),
      (∀ t : Fin N, lo ≤ t.val → t.val < hi →
        ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
      ∀ v ∈ (S ⟨hi, hhi⟩).toSubmodule, f v = 0 := by
  induction hi, hle using Nat.le_induction with
  | base =>
    intro _ _
    exact h0
  | succ k hk ih =>
    intro hhi hz
    have hkN : k < N := Nat.lt_of_succ_lt_succ hhi
    have ih' := ih (Nat.lt_succ_of_lt hkN)
      (fun t h1 h2 => hz t h1 (Nat.lt_succ_of_lt h2))
    exact GlobalTheory.CompanionTheory.Filtration.vanish_step f
      (A := S (⟨k, hkN⟩ : Fin N).castSucc) (B := S (⟨k, hkN⟩ : Fin N).succ) ih'
      (hz ⟨k, hkN⟩ hk (Nat.lt_succ_self k))

theorem intertwining_proportional :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ)
      (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
      ∀ t₀ : Fin N,
        (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) →
        (∀ t : Fin N, t ≠ t₀ →
          ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
        ∀ φ ψ : π.IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  intro G V W _ _ _ _ _ π σ N S _ hS0 hST t₀ hmult hzero φ ψ
  have happ : ∀ (f : π.IntertwiningMap σ) (v : V), f.toLinearMap v = f v :=
    fun f v => Representation.IntertwiningMap.toLinearMap_apply π σ f v
  have hbot : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S ⟨0, Nat.succ_pos N⟩).toSubmodule, f v = 0 := by
    intro f v hv
    have e0 : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by
      first
        | exact Fin.mk_zero
        | exact Fin.ext (by simp)
    rw [e0, hS0] at hv
    have hv0 : v = 0 := by
      first
        | exact (Submodule.mem_bot ℂ).1 hv
        | exact hv
        | simpa using hv
        | exact (Submodule.mem_bot ℂ).1
            ((bot_le : (⊥ : Subrepresentation π) ≤
              ⟨⊥, fun g w hw => by rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩) hv)
    rw [hv0, ← happ, map_zero]
  have htop : ∀ v : V, v ∈ (S (Fin.last N)).toSubmodule := by
    intro v
    rw [hST]
    first
      | exact Submodule.mem_top
      | trivial
      | exact (le_top : (⟨⊤, fun _ _ _ => Submodule.mem_top⟩ : Subrepresentation π) ≤ ⊤)
          (Submodule.mem_top (x := v))
      | simp
  have hlow : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f =>
    GlobalTheory.CompanionTheory.Filtration.vanish_climb S f 0 (Nat.succ_pos N) (hbot f)
      t₀.val (Nat.zero_le _) (Nat.lt_succ_of_lt t₀.isLt)
      (fun t _ ht => hzero t (by rintro rfl; exact lt_irrefl _ ht))
  have hup : ∀ f : π.IntertwiningMap σ, (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → ∀ v, f v = 0 := by
    intro f hf v
    have h := GlobalTheory.CompanionTheory.Filtration.vanish_climb S f (t₀.val + 1)
      (Nat.succ_lt_succ t₀.isLt) hf N t₀.isLt (Nat.lt_succ_self N)
      (fun t h1 _ => hzero t (by rintro rfl; exact Nat.not_succ_le_self _ h1))
    exact h v (htop v)
  have hdesc : ∀ (f : π.IntertwiningMap σ) (hf : ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0) (v : V)
      (hv : v ∈ (S t₀.succ).toSubmodule),
      (GlobalTheory.CompanionTheory.Filtration.descend f (S t₀.succ) (S t₀.castSucc) hf).toLinearMap
        (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    intro f hf v hv
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rcases hmult (GlobalTheory.CompanionTheory.Filtration.descend φ (S t₀.succ) (S t₀.castSucc) (hlow φ))
      (GlobalTheory.CompanionTheory.Filtration.descend ψ (S t₀.succ) (S t₀.castSucc) (hlow ψ)) with h | ⟨c, hc⟩
  · left
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply, happ]
    refine hup φ ?_ v
    intro w hw
    rw [← hdesc φ (hlow φ) w hw, h, LinearMap.zero_apply]
  · right
    refine ⟨c, ?_⟩
    let χ : π.IntertwiningMap σ :=
      { toLinearMap := ψ.toLinearMap - c • φ.toLinearMap
        isIntertwining' := fun g => by
          first
            | rw [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.comp_smul,
                ψ.isIntertwining' g, φ.isIntertwining' g]
            | (ext v
               have h1 := LinearMap.congr_fun (ψ.isIntertwining' g) v
               have h2 := LinearMap.congr_fun (φ.isIntertwining' g) v
               simp only [LinearMap.comp_apply] at h1 h2
               simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2,
                 map_sub, map_smul]) }
    have hχ : ∀ v, χ v = ψ v - c • φ v := by
      intro v
      rw [← happ, ← happ, ← happ]
      rfl
    have hχS : ∀ v ∈ (S t₀.succ).toSubmodule, χ v = 0 := by
      intro v hv
      rw [hχ, ← hdesc ψ (hlow ψ) v hv, ← hdesc φ (hlow φ) v hv, hc, LinearMap.smul_apply, sub_self]
    apply LinearMap.ext
    intro v
    have h := hup χ hχS v
    rw [hχ, sub_eq_zero] at h
    rw [LinearMap.smul_apply, happ, happ]
    exact h

end GlobalTheory.CompanionTheory.Filtration
