import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsProd

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.L2.Th1.H

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_reps_eq {M Λ : AddSubgroup V} {S S' : Finset V} (hS : IsReps M Λ S) (hS' : IsReps M Λ S')
    (f : V → ℂ) (hf : ∀ x ∈ Λ, ∀ u ∈ Λ, u ∈ M → f (x + u) = f x) :
    ∑ x ∈ S, f x = ∑ x ∈ S', f x := by
  obtain ⟨h1, h2, h3⟩ := hS
  obtain ⟨h1', h2', h3'⟩ := hS'
  have hg : ∀ x ∈ S, ∃ x' ∈ S', x - x' ∈ M := fun x hx => h3' x (h1 x hx)
  choose! g hgS hgM using hg
  refine Finset.sum_bij (fun x _ => g x) (fun x hx => hgS x hx) ?_ ?_ ?_
  · intro a ha b hb hab
    refine h2 a ha b hb ?_
    have e : a - b = (a - g a) - (b - g b) := by rw [hab]; abel
    rw [e]; exact M.sub_mem (hgM a ha) (hgM b hb)
  · intro b hb
    obtain ⟨a, ha, hba⟩ := h3 b (h1' b hb)
    refine ⟨a, ha, h2' _ (hgS a ha) b hb ?_⟩
    have e : g a - b = -(a - g a) - (b - a) := by abel
    rw [e]; exact M.sub_mem (M.neg_mem (hgM a ha)) hba
  · intro a ha
    have hu : g a - a ∈ M := by
      have := M.neg_mem (hgM a ha); rwa [neg_sub] at this
    have := hf a (h1 a ha) (g a - a) (Λ.sub_mem (h1' _ (hgS a ha)) (h1 a ha)) hu
    rw [show a + (g a - a) = g a by abel] at this
    exact this.symm

def tf (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (z y : V) : ℂ :=
  if z + y ∈ Λ₁ then psiT H α z y else 0

theorem tripleSum_eq (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) :
    tripleSum H α Λ₁ S₂ S₃ = ∑ z ∈ S₃, ∑ y ∈ S₂, tf H α Λ₁ z y := rfl

variable {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ Λ₃ : AddSubgroup V}

theorem tripleSum_indep (hT : TripleData H α Λ₁ Λ₂ Λ₃)
    {S₂ S₂' S₃ S₃' : Finset V} (h2 : IsReps Λ₁ Λ₂ S₂) (h2' : IsReps Λ₁ Λ₂ S₂') (h3 : IsReps Λ₂ Λ₃ S₃)
    (h3' : IsReps Λ₂ Λ₃ S₃') : tripleSum H α Λ₁ S₂ S₃ = tripleSum H α Λ₁ S₂' S₃' := by
  have hq := (psiQuadratic V H α Λ₁ Λ₂ Λ₃ hT).2.2.2
  have hyy : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, ∀ u ∈ Λ₂, u ∈ Λ₁ → tf H α Λ₁ z (y + u) = tf H α Λ₁ z y := by
    intro z hz y hy u hu2 hu1
    unfold tf
    by_cases hc : z + y ∈ Λ₁
    · have hc' : z + (y + u) ∈ Λ₁ := by rw [← add_assoc]; exact Λ₁.add_mem hc hu1
      rw [if_pos hc', if_pos hc]
      have := hq z hz y hy hc 0 (AddSubgroup.zero_mem _) u (AddSubgroup.mem_inf.2 ⟨hu1, hu2⟩) 0
        (AddSubgroup.zero_mem _)
      simpa using this
    · have hc' : z + (y + u) ∉ Λ₁ := fun h => hc (by
        have := Λ₁.sub_mem h hu1; rwa [show z + (y + u) - u = z + y by abel] at this)
      rw [if_neg hc', if_neg hc]
  have hzz : ∀ z ∈ Λ₃, ∀ t ∈ Λ₃, t ∈ Λ₂ → ∀ y ∈ Λ₂, tf H α Λ₁ (z + t) y = tf H α Λ₁ z (y + t) := by
    intro z hz t ht3 ht2 y hy
    unfold tf
    rw [show z + t + y = z + (y + t) by abel]
    by_cases hc : z + (y + t) ∈ Λ₁
    · rw [if_pos hc, if_pos hc]
      have := hq z hz (y + t) (Λ₂.add_mem hy ht2) hc 0 (AddSubgroup.zero_mem _) 0 (AddSubgroup.zero_mem _) t
        (AddSubgroup.mem_inf.2 ⟨ht2, ht3⟩)
      simpa using this
    · rw [if_neg hc, if_neg hc]
  rw [tripleSum_eq, tripleSum_eq]
  calc ∑ z ∈ S₃, ∑ y ∈ S₂, tf H α Λ₁ z y = ∑ z ∈ S₃, ∑ y ∈ S₂', tf H α Λ₁ z y :=
        Finset.sum_congr rfl fun z hz => sum_reps_eq h2 h2' _ (fun y hy u hu hu1 => hyy z (h3.1 z hz) y hy u hu hu1)
    _ = ∑ z ∈ S₃', ∑ y ∈ S₂', tf H α Λ₁ z y := by
        refine sum_reps_eq h3 h3' _ ?_
        intro z hz t ht3 ht2
        rw [show ∑ y ∈ S₂', tf H α Λ₁ (z + t) y = ∑ y ∈ S₂', tf H α Λ₁ z (y + t) from
          Finset.sum_congr rfl fun y hy => hzz z hz t ht3 ht2 y (h2'.1 y hy)]
        exact CharacterSumTripleLemmas.sum_shift h2' (tf H α Λ₁ z) (fun x hx t' ht' ht1 => hyy z hz x hx t' ht' ht1) ht2

def partP (p : V →+ V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | x ∈ Λ ∧ p x = x}
  add_mem' := fun {a b} ha hb => ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
  zero_mem' := ⟨Λ.zero_mem, map_zero p⟩
  neg_mem' := fun {a} ha => ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2]⟩

def partQ (p : V →+ V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | x ∈ Λ ∧ p x = 0}
  add_mem' := fun {a b} ha hb => ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨Λ.zero_mem, map_zero p⟩
  neg_mem' := fun {a} ha => ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2, neg_zero]⟩

theorem mem_partP {p : V →+ V} {Λ : AddSubgroup V} {x : V} : x ∈ partP p Λ ↔ x ∈ Λ ∧ p x = x := Iff.rfl

theorem mem_of_mul {M Λ : AddSubgroup V} (m m' r : V →+ V) (e : ℕ) (inv : ∀ x, m' (m x) = x + e • r x)
    (hm'M : ∀ x ∈ M, m' x ∈ M) (her : ∀ x ∈ Λ, e • r x ∈ M) {x : V} (hx : x ∈ Λ) (hmx : m x ∈ M) : x ∈ M := by
  have a1 := hm'M _ hmx
  rw [inv] at a1
  have := M.sub_mem a1 (her x hx)
  rwa [show x + e • r x - e • r x = x by abel] at this

theorem reps_image_mul {M Λ : AddSubgroup V} {S : Finset V} (hS : IsReps M Λ S) (m m' r : V →+ V) (e : ℕ)
    (inv : ∀ x, m' (m x) = x + e • r x) (inv' : ∀ x, m (m' x) = x + e • r x)
    (hmΛ : ∀ x ∈ Λ, m x ∈ Λ) (hm'Λ : ∀ x ∈ Λ, m' x ∈ Λ) (hmM : ∀ x ∈ M, m x ∈ M) (hm'M : ∀ x ∈ M, m' x ∈ M)
    (her : ∀ x ∈ Λ, e • r x ∈ M) : IsReps M Λ (S.image m) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    exact hmΛ x (h1 x hx)
  · intro w hw w' hw' hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hw'
    have hxx : x - x' ∈ M :=
      mem_of_mul m m' r e inv hm'M her (Λ.sub_mem (h1 x hx) (h1 x' hx')) (by rw [map_sub]; exact hd)
    rw [h2 x hx x' hx' hxx]
  · intro y hy
    obtain ⟨x, hx, hd⟩ := h3 (m' y) (hm'Λ y hy)
    refine ⟨m x, Finset.mem_image.2 ⟨x, hx, rfl⟩, ?_⟩
    have a1 := hmM _ hd
    rw [map_sub, inv'] at a1
    have e2 : y - m x = (y + e • r y - m x) - e • r y := by abel
    rw [e2]; exact M.sub_mem a1 (her y hy)

theorem reps_image_inv {M Λ Λ' : AddSubgroup V} {S : Finset V} (hS : IsReps M Λ S) (σ : V →+ V)
    (hσσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ') (hΛ' : ∀ x ∈ Λ', σ x ∈ Λ) (hM : ∀ x ∈ M, σ x ∈ M) :
    IsReps M Λ' (S.image σ) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    exact hΛ x (h1 x hx)
  · intro w hw w' hw' hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hw'
    have := hM _ hd
    rw [map_sub, hσσ, hσσ] at this
    rw [h2 x hx x' hx' this]
  · intro y hy
    obtain ⟨x, hx, hd⟩ := h3 (σ y) (hΛ' y hy)
    refine ⟨σ x, Finset.mem_image.2 ⟨x, hx, rfl⟩, ?_⟩
    have := hM _ hd
    rwa [map_sub, hσσ] at this

theorem reps_prod {M Λ : AddSubgroup V} (p : V →+ V) (hpp : ∀ x, p (p x) = p x) (hpΛ : ∀ x ∈ Λ, p x ∈ Λ)
    (hpM : ∀ x ∈ M, p x ∈ M) {A B : Finset V} (hA : IsReps M (partP p Λ) A) (hB : IsReps M (partQ p Λ) B) :
    IsReps M Λ ((A ×ˢ B).image fun w => w.1 + w.2) :=
  _root_.UpperTheory.Reformulated.B.P9.reps_prod p hpp hpΛ hpM hA hB

theorem orthH (p : V →+ V) (hporth : ∀ x y, H (p x) (y - p y) = 0) {u v : V} (hu : p u = u) (hv : p v = 0) :
    H u v = 0 := by
  have := hporth u v
  rwa [hv, sub_zero, hu] at this

theorem psi_split (hT : TripleData H α Λ₁ Λ₂ Λ₃) (p : V →+ V) (hporth : ∀ x y, H (p x) (y - p y) = 0)
    {a₂ a₃ b₂ b₃ : V} (ha₂ : a₂ ∈ partP p Λ₂) (ha₃ : a₃ ∈ partP p Λ₃) (hb₂ : b₂ ∈ partQ p Λ₂)
    (hb₃ : b₃ ∈ partQ p Λ₃) (h1 : a₃ + a₂ ∈ Λ₁) (h1' : b₃ + b₂ ∈ Λ₁) :
    psiT H α (a₃ + b₃) (a₂ + b₂) = psiT H α a₃ a₂ * psiT H α b₃ b₂ := by
  have hH1 : H a₃ b₂ = 0 := orthH p hporth ha₃.2 hb₂.2
  have hH2 : H b₃ a₂ = 0 := by rw [hT.herm a₂ b₃, orthH p hporth ha₂.2 hb₃.2, map_zero]
  have hH3 : H a₃ b₃ = 0 := orthH p hporth ha₃.2 hb₃.2
  have hH4 : H a₂ b₂ = 0 := orthH p hporth ha₂.2 hb₂.2
  have hH5 : H (a₃ + a₂) (b₃ + b₂) = 0 :=
    orthH p hporth (by rw [map_add, ha₃.2, ha₂.2]) (by rw [map_add, hb₃.2, hb₂.2, add_zero])
  have e3 := hT.sc₃.2 a₃ ha₃.1 b₃ hb₃.1
  have e2 := hT.sc₂.2 a₂ ha₂.1 b₂ hb₂.1
  have e1 := hT.sc₁.2 _ h1 _ h1'
  simp only [altE, hH3, hH4, hH5, Complex.zero_im, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one] at e1 e2 e3
  have him : altE H (a₃ + b₃) (a₂ + b₂) = altE H a₃ a₂ + altE H b₃ b₂ := by
    simp only [altE, map_add, LinearMap.add_apply, hH1, hH2, add_zero, zero_add, Complex.add_im]
  unfold psiT
  rw [e3, e2, show a₃ + b₃ + (a₂ + b₂) = (a₃ + a₂) + (b₃ + b₂) by abel, e1, him, Complex.ofReal_add, mul_add,
    Complex.exp_add]
  ring

theorem tripleSum_prod (hT : TripleData H α Λ₁ Λ₂ Λ₃) (p : V →+ V) (hporth : ∀ x y, H (p x) (y - p y) = 0)
    (hp1 : ∀ x ∈ Λ₁, p x ∈ Λ₁) {A₂ A₃ B₂ B₃ : Finset V} (hA₂ : ∀ x ∈ A₂, x ∈ partP p Λ₂)
    (hA₃ : ∀ x ∈ A₃, x ∈ partP p Λ₃) (hB₂ : ∀ x ∈ B₂, x ∈ partQ p Λ₂) (hB₃ : ∀ x ∈ B₃, x ∈ partQ p Λ₃) :
    tripleSum H α Λ₁ ((A₂ ×ˢ B₂).image fun w => w.1 + w.2) ((A₃ ×ˢ B₃).image fun w => w.1 + w.2)
      = tripleSum H α Λ₁ A₂ A₃ * tripleSum H α Λ₁ B₂ B₃ := by
  have hinj : ∀ {A B : Finset V}, (∀ x ∈ A, p x = x) → (∀ x ∈ B, p x = 0) →
      Set.InjOn (fun w : V × V => w.1 + w.2) ↑(A ×ˢ B) := by
    intro A B hA hB w hw w' hw' h
    rw [Finset.coe_product, Set.mem_prod] at hw hw'
    have h' := congrArg p h
    simp only [map_add, hA _ hw.1, hB _ hw.2, hA _ hw'.1, hB _ hw'.2, add_zero] at h'
    have h2 : w.2 = w'.2 := by simp only at h; rw [h'] at h; exact add_left_cancel h
    exact Prod.ext h' h2
  have hS2 : ∀ g : V → ℂ, ∑ y ∈ (A₂ ×ˢ B₂).image (fun w => w.1 + w.2), g y = ∑ w ∈ A₂ ×ˢ B₂, g (w.1 + w.2) :=
    fun g => Finset.sum_image (hinj (fun x hx => (hA₂ x hx).2) (fun x hx => (hB₂ x hx).2))
  have hS3 : ∀ g : V → ℂ, ∑ y ∈ (A₃ ×ˢ B₃).image (fun w => w.1 + w.2), g y = ∑ w ∈ A₃ ×ˢ B₃, g (w.1 + w.2) :=
    fun g => Finset.sum_image (hinj (fun x hx => (hA₃ x hx).2) (fun x hx => (hB₃ x hx).2))
  have hpt : ∀ a₃ ∈ A₃, ∀ b₃ ∈ B₃, ∀ a₂ ∈ A₂, ∀ b₂ ∈ B₂,
      tf H α Λ₁ (a₃ + b₃) (a₂ + b₂) = tf H α Λ₁ a₃ a₂ * tf H α Λ₁ b₃ b₂ := by
    intro a₃ ha₃ b₃ hb₃ a₂ ha₂ b₂ hb₂
    unfold tf
    have ex : a₃ + b₃ + (a₂ + b₂) = (a₃ + a₂) + (b₃ + b₂) := by abel
    by_cases c1 : a₃ + a₂ ∈ Λ₁
    · by_cases c2 : b₃ + b₂ ∈ Λ₁
      · rw [if_pos (by rw [ex]; exact Λ₁.add_mem c1 c2), if_pos c1, if_pos c2]
        exact psi_split hT p hporth (hA₂ _ ha₂) (hA₃ _ ha₃) (hB₂ _ hb₂) (hB₃ _ hb₃) c1 c2
      · rw [if_neg c2, mul_zero, if_neg]
        intro h; apply c2
        rw [ex] at h
        have := Λ₁.sub_mem h c1
        rwa [show a₃ + a₂ + (b₃ + b₂) - (a₃ + a₂) = b₃ + b₂ by abel] at this
    · rw [if_neg c1, zero_mul, if_neg]
      intro h; apply c1
      have := hp1 _ h
      simp only [map_add, (hA₃ _ ha₃).2, (hB₃ _ hb₃).2, (hA₂ _ ha₂).2, (hB₂ _ hb₂).2, add_zero] at this
      exact this
  rw [tripleSum_eq, tripleSum_eq, tripleSum_eq]
  simp only [hS2, hS3]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a₃ ha₃ => ?_
  refine Finset.sum_congr rfl fun b₃ hb₃ => ?_
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a₂ ha₂ => ?_
  exact Finset.sum_congr rfl fun b₂ hb₂ => hpt a₃ ha₃ b₃ hb₃ a₂ ha₂ b₂ hb₂

theorem tripleSum_inv (σ : V →+ V) (hσσ : ∀ x, σ (σ x) = x) (hσH : ∀ x y, H (σ x) (σ y) = H x y)
    (hσα : ∀ x, α (σ x) = α x) (hσ1 : ∀ x ∈ Λ₁, σ x ∈ Λ₁) (A₂ A₃ : Finset V) :
    tripleSum H α Λ₁ (A₂.image σ) (A₃.image σ) = tripleSum H α Λ₁ A₂ A₃ := by
  have hinj : ∀ A : Finset V, Set.InjOn σ ↑A := fun A x _ y _ h => by rw [← hσσ x, h, hσσ]
  rw [tripleSum_eq, tripleSum_eq, Finset.sum_image (hinj A₃)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_image (hinj A₂)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hc : σ z + σ y ∈ Λ₁ ↔ z + y ∈ Λ₁ := by
    rw [← map_add]
    exact ⟨fun h => by have := hσ1 _ h; rwa [hσσ] at this, fun h => hσ1 _ h⟩
  unfold tf
  by_cases h : z + y ∈ Λ₁
  · rw [if_pos (hc.2 h), if_pos h]
    unfold psiT altE
    rw [← map_add, hσα, hσα, hσα, hσH]
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

theorem tripleSum_conj (hT : TripleData H α Λ₁ Λ₂ Λ₃) (m m' r : V →+ V) (e : ℕ)
    (inv : ∀ x, m' (m x) = x + e • r x) (hm1 : ∀ x ∈ Λ₁, m x ∈ Λ₁) (hm'1 : ∀ x ∈ Λ₁, m' x ∈ Λ₁)
    (her2 : ∀ x ∈ Λ₂, e • r x ∈ Λ₁) (her3 : ∀ x ∈ Λ₃, e • r x ∈ Λ₁)
    (hmα1 : ∀ x ∈ Λ₁, α (m x) = α x) (hmα2 : ∀ x ∈ Λ₂, α (m x) = α x) (hmα3 : ∀ x ∈ Λ₃, α (m x) = α x)
    (hmH : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, ∃ k : ℤ, altE H (m z) (m y) = -altE H z y + 2 * k)
    {A₂ A₃ : Finset V} (hA₂ : ∀ x ∈ A₂, x ∈ Λ₂) (hA₃ : ∀ x ∈ A₃, x ∈ Λ₃)
    (hi₂ : Set.InjOn m ↑A₂) (hi₃ : Set.InjOn m ↑A₃) :
    tripleSum H α Λ₁ (A₂.image m) (A₃.image m) = conj (tripleSum H α Λ₁ A₂ A₃) := by
  have hreal : ∀ {Λ : AddSubgroup V}, IsSemiChar H Λ α → ∀ x ∈ Λ, conj (α x) = α x := by
    intro Λ hs x hx
    rcases hs.1 x hx with h | h <;> rw [h] <;> simp
  rw [tripleSum_eq, tripleSum_eq, Finset.sum_image hi₃, map_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.sum_image hi₂, map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hz3 := hA₃ z hz
  have hy2 := hA₂ y hy
  have hc : m z + m y ∈ Λ₁ ↔ z + y ∈ Λ₁ := by
    rw [show m z + m y = m (z + y) from (map_add m z y).symm]
    refine ⟨fun h => ?_, fun h => hm1 _ h⟩
    have a1 := hm'1 _ h
    rw [inv, map_add, smul_add] at a1
    have := Λ₁.sub_mem a1 (Λ₁.add_mem (her3 z hz3) (her2 y hy2))
    rwa [show z + y + (e • r z + e • r y) - (e • r z + e • r y) = z + y by abel] at this
  unfold tf
  by_cases h : z + y ∈ Λ₁
  · rw [if_pos (hc.2 h), if_pos h]
    obtain ⟨k, hk⟩ := hmH z hz3 y hy2
    unfold psiT
    rw [show m z + m y = m (z + y) from (map_add m z y).symm, hmα1 _ h, hmα2 _ hy2, hmα3 _ hz3, hk, map_mul, map_mul, map_mul,
      hreal hT.sc₁ _ h, hreal hT.sc₂ _ hy2, hreal hT.sc₃ _ hz3, ← Complex.exp_conj]
    congr 1
    refine Complex.exp_eq_exp_iff_exists_int.2 ⟨-k, ?_⟩
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h, map_zero]

structure SignData (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) (p σ m m' r : V →+ V) (e : ℕ) : Prop where
  pp : ∀ x, p (p x) = p x
  porth : ∀ x y, H (p x) (y - p y) = 0
  p1 : ∀ x ∈ Λ₁, p x ∈ Λ₁
  p2 : ∀ x ∈ Λ₂, p x ∈ Λ₂
  p3 : ∀ x ∈ Λ₃, p x ∈ Λ₃
  σσ : ∀ x, σ (σ x) = x
  σp : ∀ x, p (σ x) = σ x - σ (p x)
  σH : ∀ x y, H (σ x) (σ y) = H x y
  σα : ∀ x, α (σ x) = α x
  σ1 : ∀ x ∈ Λ₁, σ x ∈ Λ₁
  σ2 : ∀ x ∈ Λ₂, σ x ∈ Λ₂
  σ3 : ∀ x ∈ Λ₃, σ x ∈ Λ₃
  mp : ∀ x, m (p x) = p (m x)
  m'p : ∀ x, m' (p x) = p (m' x)
  m1 : ∀ x ∈ Λ₁, m x ∈ Λ₁
  m2 : ∀ x ∈ Λ₂, m x ∈ Λ₂
  m3 : ∀ x ∈ Λ₃, m x ∈ Λ₃
  m'1 : ∀ x ∈ Λ₁, m' x ∈ Λ₁
  m'2 : ∀ x ∈ Λ₂, m' x ∈ Λ₂
  m'3 : ∀ x ∈ Λ₃, m' x ∈ Λ₃
  r2 : ∀ x ∈ Λ₂, r x ∈ Λ₂
  r3 : ∀ x ∈ Λ₃, r x ∈ Λ₃
  inv : ∀ x, m' (m x) = x + e • r x
  inv' : ∀ x, m (m' x) = x + e • r x
  e21 : ∀ x ∈ Λ₂, e • x ∈ Λ₁
  e31 : ∀ x ∈ Λ₃, e • x ∈ Λ₁
  e32 : ∀ x ∈ Λ₃, e • x ∈ Λ₂
  mα1 : ∀ x ∈ Λ₁, α (m x) = α x
  mα2 : ∀ x ∈ Λ₂, α (m x) = α x
  mα3 : ∀ x ∈ Λ₃, α (m x) = α x
  mH : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, ∃ k : ℤ, altE H (m z) (m y) = -altE H z y + 2 * k

theorem relIdx_smul_mem {M Λ : AddSubgroup V} {x : V} (hx : x ∈ Λ) : relIdx M Λ • x ∈ M := by
  have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf Λ) (⟨x, hx⟩ : Λ)
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul] at this
  exact this

theorem exists_e (hT : TripleData H α Λ₁ Λ₂ Λ₃) :
    ∃ e : ℕ, 0 < e ∧ (∀ x ∈ Λ₂, e • x ∈ Λ₁) ∧ (∀ x ∈ Λ₃, e • x ∈ Λ₁) ∧ (∀ x ∈ Λ₃, e • x ∈ Λ₂) := by
  refine ⟨relIdx Λ₁ Λ₂ * relIdx Λ₁ Λ₃ * relIdx Λ₂ Λ₃,
    Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hT.i₁₂ hT.i₁₃) hT.i₂₃), ?_, ?_, ?_⟩
  · intro x hx
    have h := Λ₁.nsmul_mem (relIdx_smul_mem (M := Λ₁) hx) (relIdx Λ₁ Λ₃ * relIdx Λ₂ Λ₃)
    rw [smul_smul] at h
    convert h using 2; ring
  · intro x hx
    have h := Λ₁.nsmul_mem (relIdx_smul_mem (M := Λ₁) hx) (relIdx Λ₁ Λ₂ * relIdx Λ₂ Λ₃)
    rw [smul_smul] at h
    convert h using 2; ring
  · intro x hx
    have h := Λ₂.nsmul_mem (relIdx_smul_mem (M := Λ₂) hx) (relIdx Λ₁ Λ₂ * relIdx Λ₁ Λ₃)
    rw [smul_smul] at h
    convert h using 2

theorem tripleMu_eq_one {p σ m m' r : V →+ V} {e : ℕ} (hT : TripleData H α Λ₁ Λ₂ Λ₃)
    (hF : ∃ F ∈ fixedBy H α Λ₁, F ≠ 0) (hD : SignData H α Λ₁ Λ₂ Λ₃ p σ m m' r e)
    {S₂ S₃ : Finset V} (h2 : IsReps Λ₁ Λ₂ S₂) (h3 : IsReps Λ₂ Λ₃ S₃) : tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ = 1 := by
  have hi2 : relIdx Λ₁ (partP p Λ₂) ≠ 0 := fun h =>
    hT.i₁₂ (AddSubgroup.relIndex_eq_zero_of_le_right (fun x hx => (mem_partP.1 hx).1) h)
  have hi3 : relIdx Λ₂ (partP p Λ₃) ≠ 0 := fun h =>
    hT.i₂₃ (AddSubgroup.relIndex_eq_zero_of_le_right (fun x hx => (mem_partP.1 hx).1) h)
  obtain ⟨A₂, hA₂⟩ := (repsExist V Λ₁ (partP p Λ₂) hi2).1
  obtain ⟨A₃, hA₃⟩ := (repsExist V Λ₂ (partP p Λ₃) hi3).1
  have pq : ∀ {Λ : AddSubgroup V}, (∀ x ∈ Λ, σ x ∈ Λ) → ∀ x ∈ partP p Λ, σ x ∈ partQ p Λ :=
    fun hσ x hx => ⟨hσ x hx.1, by rw [hD.σp, hx.2, sub_self]⟩
  have qp : ∀ {Λ : AddSubgroup V}, (∀ x ∈ Λ, σ x ∈ Λ) → ∀ x ∈ partQ p Λ, σ x ∈ partP p Λ :=
    fun hσ x hx => ⟨hσ x hx.1, by rw [hD.σp, hx.2, map_zero, sub_zero]⟩
  have mP : ∀ {Λ : AddSubgroup V} {f : V →+ V}, (∀ x, f (p x) = p (f x)) → (∀ x ∈ Λ, f x ∈ Λ) →
      ∀ x ∈ partP p Λ, f x ∈ partP p Λ :=
    fun hfp hf x hx => ⟨hf x hx.1, by rw [← hfp, hx.2]⟩
  have hB₂ := reps_image_inv hA₂ σ hD.σσ (pq hD.σ2) (qp hD.σ2) hD.σ1
  have hB₃ := reps_image_inv hA₃ σ hD.σσ (pq hD.σ3) (qp hD.σ3) hD.σ2
  have hC₂ := reps_image_mul hA₂ m m' r e hD.inv hD.inv' (mP hD.mp hD.m2) (mP hD.m'p hD.m'2) hD.m1 hD.m'1
    (fun x hx => hD.e21 _ (hD.r2 _ hx.1))
  have hC₃ := reps_image_mul hA₃ m m' r e hD.inv hD.inv' (mP hD.mp hD.m3) (mP hD.m'p hD.m'3) hD.m2 hD.m'2
    (fun x hx => hD.e32 _ (hD.r3 _ hx.1))
  have hP₂ := reps_prod p hD.pp hD.p2 hD.p1 hA₂ hB₂
  have hP₃ := reps_prod p hD.pp hD.p3 hD.p2 hA₃ hB₃
  have hQ₂ := reps_prod p hD.pp hD.p2 hD.p1 hC₂ hB₂
  have hQ₃ := reps_prod p hD.pp hD.p3 hD.p2 hC₃ hB₃
  have hinj : ∀ {M Λ : AddSubgroup V} {A : Finset V}, IsReps M Λ A → (∀ x ∈ M, m' x ∈ M) →
      (∀ x ∈ Λ, e • r x ∈ M) → Set.InjOn m ↑A := by
    intro M Λ A hA hm' her x hx y hy hxy
    refine hA.2.1 x hx y hy (mem_of_mul m m' r e hD.inv hm' her (Λ.sub_mem (hA.1 x hx) (hA.1 y hy)) ?_)
    rw [map_sub, hxy, sub_self]; exact M.zero_mem
  have eσ := tripleSum_inv (H := H) (Λ₁ := Λ₁) σ hD.σσ hD.σH hD.σα hD.σ1 A₂ A₃
  have eP := tripleSum_prod hT p hD.porth hD.p1 hA₂.1 hA₃.1 hB₂.1 hB₃.1
  have eQ := tripleSum_prod hT p hD.porth hD.p1 hC₂.1 hC₃.1 hB₂.1 hB₃.1
  have eC := tripleSum_conj hT m m' r e hD.inv hD.m1 hD.m'1 (fun x hx => hD.e21 _ (hD.r2 _ hx))
    (fun x hx => hD.e31 _ (hD.r3 _ hx)) hD.mα1 hD.mα2 hD.mα3 hD.mH (fun x hx => (hA₂.1 x hx).1)
    (fun x hx => (hA₃.1 x hx).1) (hinj hA₂ hD.m'1 (fun x hx => hD.e21 _ (hD.r2 _ hx.1)))
    (hinj hA₃ hD.m'2 (fun x hx => hD.e32 _ (hD.r3 _ hx.1)))
  have hS : tripleSum H α Λ₁ S₂ S₃ = ((Complex.normSq (tripleSum H α Λ₁ A₂ A₃) : ℝ) : ℂ) := by
    rw [tripleSum_indep hT h2 hQ₂ h3 hQ₃, eQ, eC, eσ, Complex.normSq_eq_conj_mul_self]
  have h8 := tripleEighth V H α Λ₁ Λ₂ Λ₃ hT hF S₂ S₃ h2 h3
  unfold tripleMu at h8 ⊢
  rw [hS, ← Complex.ofReal_mul] at h8 ⊢
  rw [← Complex.ofReal_pow, Complex.ofReal_eq_one] at h8
  have hnn : 0 ≤ Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃))
      * Complex.normSq (tripleSum H α Λ₁ A₂ A₃) :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (Complex.normSq_nonneg _)
  rw [(pow_eq_one_iff_of_nonneg hnn (by norm_num)).1 h8, Complex.ofReal_one]

end Formalism.L2.PairingIndexBounds.Eq.Mu
