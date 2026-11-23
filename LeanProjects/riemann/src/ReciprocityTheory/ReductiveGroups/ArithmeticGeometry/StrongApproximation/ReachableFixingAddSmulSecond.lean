import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.ConjMemEichSet

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

variable (σ J) in

def Reach (e f : ι → K) {s : ℕ} (a : Fin s → ι → K) (b b' : ι → K) : Prop :=
  ∃ p ∈ Good σ J e f, (∀ j, p *ᵥ a j = a j) ∧ p *ᵥ b = b'

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef

theorem reach_refl (b : ι → K) : Reach σ J e f a b b := by
  have h1 : (1 : Matrix ι ι K) ∈ Good σ J e f :=
    ⟨1, Submonoid.one_mem _, 1, 1, by simp, by simp [tor]⟩
  exact ⟨1, h1, fun j => Matrix.one_mulVec _, Matrix.one_mulVec _⟩

theorem reach_trans {b b' b'' : ι → K} (h1 : Reach σ J e f a b b') (h2 : Reach σ J e f a b' b'') :
    Reach σ J e f a b b'' := by
  obtain ⟨p1, hp1, ha1, hb1⟩ := h1
  obtain ⟨p2, hp2, ha2, hb2⟩ := h2
  refine ⟨p2 * p1, (by apply good_mul <;> assumption), fun j => ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ha1, ha2]
  · rw [← Matrix.mulVec_mulVec, hb1, hb2]

theorem reach_symm {b b' : ι → K} (h : Reach σ J e f a b b') : Reach σ J e f a b' b := by
  obtain ⟨p, hp, ha, hb⟩ := h
  obtain ⟨g', hg', hg'p, -⟩ : ∃ g' ∈ Good σ J e f, g' * p = 1 ∧ p * g' = 1 := by
    apply good_inv <;> assumption
  refine ⟨g', hg', fun j => ?_, ?_⟩
  · conv_lhs => rw [← ha j]
    rw [Matrix.mulVec_mulVec, hg'p, Matrix.one_mulVec]
  · rw [← hb, Matrix.mulVec_mulVec, hg'p, Matrix.one_mulVec]

include hae haf

theorem reach_eich_e {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J e u c *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  refine ⟨eich σ J e u c,
    (by apply good_of_closure <;> first
      | exact Submonoid.subset_closure (Or.inl ⟨u, c, hue, huf, hc, rfl⟩) | assumption),
    fun j => ?_, rfl⟩
  rw [hE, hae j, ← hf_symm hσ hJ u (a j), hua j, map_zero]
  simp

theorem reach_eich_f {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J f u c *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  refine ⟨eich σ J f u c,
    (by apply good_of_closure <;> first
      | exact Submonoid.subset_closure (Or.inr ⟨u, c, huf, hue, hc, rfl⟩) | assumption),
    fun j => ?_, rfl⟩
  rw [hE, haf j, ← hf_symm hσ hJ u (a j), hua j, map_zero]
  simp

theorem reach_tor {l m : K} (hml : m * σ l = 1) (b : ι → K) :
    Reach σ J e f a b (tor σ J e f l m *ᵥ b) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  refine ⟨tor σ J e f l m, (by apply good_tor <;> assumption), fun j => ?_, rfl⟩
  simp only [tor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hvmv, hdot,
    haf j, hae j, zero_smul, smul_zero, add_zero]

theorem reachableFixing_add_smul_first {c : K} (hc : σ c = -c) (b : ι → K) :
    Reach σ J e f a b (b + (c * hf σ J b e) • e) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have h0 : ∀ v : ι → K, hf σ J 0 v = 0 := fun v => by simp [hf]
  have h0' : ∀ v : ι → K, hf σ J v 0 = 0 := fun v => by simp [hf]
  have := reach_eich_e hσ hJ he hff hef hae haf (u := 0) (c := c) (h0 e) (h0 f)
    (by rw [hc, h0]; ring) (fun j => h0 _) b
  convert this using 1
  rw [hE, h0']
  simp

theorem reachableFixing_add_smul_second {c : K} (hc : σ c = -c) (b : ι → K) :
    Reach σ J e f a b (b + (c * hf σ J b f) • f) := by
  have hvmv : ∀ x y v : ι → K, vecMulVec x y *ᵥ v = (y ⬝ᵥ v) • x := by
    intro x y v
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ g v : ι → K, (J *ᵥ (σ ∘ g)) ⬝ᵥ v = hf σ J v g := by
    intro g v
    simp only [dotProduct, mulVec, hf, Function.comp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : ∀ (g w v : ι → K) (d : K), eich σ J g w d *ᵥ v =
      v + hf σ J v g • w - hf σ J v w • g + (d * hf σ J v g) • g := by
    intro g w v d
    simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hvmv, hdot, smul_smul]
  have h0 : ∀ v : ι → K, hf σ J 0 v = 0 := fun v => by simp [hf]
  have h0' : ∀ v : ι → K, hf σ J v 0 = 0 := fun v => by simp [hf]
  have := reach_eich_f hσ hJ he hff hef hae haf (u := 0) (c := c) (h0 e) (h0 f)
    (by rw [hc, h0]; ring) (fun j => h0 _) b
  convert this using 1
  rw [hE, h0']
  simp

theorem good_preserves {p : Matrix ι ι K} (hp : p ∈ Good σ J e f) (x y : ι → K) :
    hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hp
  have key : ∀ g ∈ Submonoid.closure (eichSet σ J e f), ∀ x y : ι → K,
      hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      intro x y
      rcases hg with ⟨u, c, hue, huf, hc, rfl⟩ | ⟨u, c, huf, hue, hc, rfl⟩
      · apply eich_preserves <;> assumption
      · apply eich_preserves <;> assumption
    | one => intro x y; simp
    | mul g h _ _ ihg ihh =>
      intro x y
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ihg, ihh]
  have ht : ∀ x y : ι → K, hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by
    intro x y
    apply tor_preserves <;> assumption
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key n hn, ht]

theorem reach_inv {b b' : ι → K} (h : Reach σ J e f a b b') (hb : ∀ j, hf σ J b (a j) = 0) :
    (∀ j, hf σ J b' (a j) = 0) ∧ hf σ J b' b' = hf σ J b b := by
  obtain ⟨p, hp, ha, rfl⟩ := h
  refine ⟨fun j => ?_, good_preserves hσ hJ he hff hef hae haf hp b b⟩
  rw [← ha j, good_preserves hσ hJ he hff hef hae haf hp, hb]

end

end ReciprocityTheory.ChartRestriction.G.SA
