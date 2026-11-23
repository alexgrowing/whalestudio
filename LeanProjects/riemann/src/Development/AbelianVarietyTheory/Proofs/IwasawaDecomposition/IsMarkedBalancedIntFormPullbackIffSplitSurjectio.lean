import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.SplitPull

theorem apply_eq_zero_of_isotropic {X : Type} [AddCommGroup X] {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) {d : X} (hd : x d d = 0) (z : X) : x d z = 0 := by
  by_contra h
  have h1 := hp ((-(x d z * (x z z + 1))) • d + z)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hd, hs z d] at h1
  have h2 : 1 ≤ x d z * x d z := mul_self_pos.2 h
  have h3 := hp z
  nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ x z z + 1 by omega)]

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
  {r : X →ₗ[O] X₁} {s : X₁ →ₗ[O] X}

def pullHom (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_pull (h : ∀ a, r (s a) = a) (β : LinearMap.BilinForm ℤ X₁) : pull s (pull r β) = β :=
  LinearMap.ext₂ fun a b => by simp [h]

theorem pull_injective (h : ∀ a, r (s a) = a) : Function.Injective (pull r) :=
  Function.LeftInverse.injective (pull_pull h)

theorem eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) (hv : ∀ y, pull r β y y = 0 → x y y = 0) :
    pull r (pull s x) = x := by
  have key : ∀ a z, x (s (r a)) z = x a z := fun a z => by
    have := apply_eq_zero_of_isotropic hs hp (hv (a - s (r a)) (by simp [h])) z
    rw [map_sub, LinearMap.sub_apply] at this
    omega
  refine LinearMap.ext₂ fun a b => ?_
  rw [pull_apply, pull_apply, key, hs, key, hs]

variable [Module.Finite O X] [Module.Finite O X₁]

theorem inFace_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    InFace bar ψ lab (pull r β) (pull r x) ↔ InFace bar ψ lab β x := by
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have e : pull r β + pull r x = pull r (β + x) := rfl
  unfold InFace
  rw [e]
  simp only [evalZ_pull _ hr, pull_apply]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ x y y)).symm
    (and_congr (hr.forall (p := fun y => β y y = 0 → x y y = 0)).symm Iff.rfl))
  rw [← pull_pull h x]
  exact pull_mem s hx

theorem InFace_eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hx : InFace bar ψ lab (pull r β) x) : ∃ x₁, pull r x₁ = x :=
  ⟨_, eq_pull h hx.1.1 hx.2.1 hx.2.2.1⟩

theorem isIndec_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    IsIndec bar ψ lab (pull r β) (pull r x) ↔ IsIndec bar ψ lab β x := by
  have hne : ∀ y : LinearMap.BilinForm ℤ X₁, pull r y ≠ 0 ↔ y ≠ 0 := fun y =>
    (pull_injective h).ne_iff' (rfl : pull r 0 = 0)
  refine and_congr (inFace_pull_iff h) (and_congr (hne x) ⟨fun H y z hy hz y0 z0 e => ?_, fun H y z hy hz y0 z0 e => ?_⟩)
  · exact H _ _ ((inFace_pull_iff h).2 hy) ((inFace_pull_iff h).2 hz) ((hne y).2 y0) ((hne z).2 z0) (by rw [← e]; rfl)
  · obtain ⟨y, rfl⟩ := InFace_eq_pull h hy
    obtain ⟨z, rfl⟩ := InFace_eq_pull h hz
    exact H y z ((inFace_pull_iff h).1 hy) ((inFace_pull_iff h).1 hz) ((hne y).1 y0) ((hne z).1 z0)
      (pull_injective h e)

theorem isMarked_pull_iff' (h : ∀ a, r (s a) = a) (i : ℕ) (β : LinearMap.BilinForm ℤ X₁) :
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  classical
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have hsum : ∀ S : Finset (LinearMap.BilinForm ℤ X₁), ∑ x ∈ S.map ⟨pull r, pull_injective h⟩, x = pull r (∑ x ∈ S, x) :=
    fun S => by
      rw [Finset.sum_map]
      exact (map_sum (pullHom r) (fun x => x) S).symm
  unfold IsMarked
  rw [evalZ_pull _ hr]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ β y y)).symm
    (and_congr ⟨fun H k β' e => H k (pull r β') (by rw [← e]; rfl), fun H k β' e => H k (pull s β') ?_⟩
      (and_congr Iff.rfl ⟨?_, ?_⟩)))
  · rw [← pull_pull h β]
    exact pull_mem s hx
  · rw [← pull_pull h β, ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    have hS' : (S.preimage (pull r) (pull_injective h).injOn).map ⟨pull r, pull_injective h⟩ = S := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ?_⟩
      obtain ⟨y, rfl⟩ := InFace_eq_pull h ((hS x).1 hx).1
      exact ⟨y, hx, rfl⟩
    refine ⟨S.preimage (pull r) (pull_injective h).injOn, fun x => ?_, k, hk, pull_injective h ?_⟩
    · rw [Finset.mem_preimage, hS, isIndec_pull_iff h]
    · rw [← hsum, hS', ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    refine ⟨S.map ⟨pull r, pull_injective h⟩, fun x => ?_, k, hk, ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (isIndec_pull_iff h).2 ((hS y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := InFace_eq_pull h hx.1
        exact ⟨y, (hS y).2 ((isIndec_pull_iff h).1 hx), rfl⟩
    · rw [hsum, ← e]; rfl

theorem isMarked_pull_iff : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁,
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β :=
  fun _ _ _ _ _ i _ _ _ _ _ _ _ _ _ _ h β => isMarked_pull_iff' h i β

end GlobalTheory.PolFan.Mark.SplitPull
