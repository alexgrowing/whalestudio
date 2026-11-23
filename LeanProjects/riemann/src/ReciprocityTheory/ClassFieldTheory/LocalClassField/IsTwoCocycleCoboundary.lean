import Mathlib
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

section Alg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)

def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

def D1 (y : G → A) (g h : G) : A := ρ g (y h) - y (g * h) + y g

variable {ρ}

theorem IsTwoCocycle.sub {c c' : G → G → A} (hc : IsTwoCocycle ρ c) (hc' : IsTwoCocycle ρ c') :
    IsTwoCocycle ρ (fun g h => c g h - c' g h) := by
  intro g h k
  have h1 := hc g h k
  have h2 := hc' g h k
  simp only [map_sub]
  linear_combination (norm := abel) h1 - h2

variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)

include hrs hr in
theorem s_mem {n : G} (hn : n ∈ N) : s n ∈ N := by
  have h : s n = (r n)⁻¹ * n := by rw [eq_inv_mul_iff_mul_eq, hrs]
  rw [h]; exact N.mul_mem (N.inv_mem (hr n)) hn

include hc hrs hr hrn hsn in

theorem stepA (h0 : ∀ n ∈ N, ∀ m ∈ N, c n m = 0) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => - c (r x) (s x)) n g = 0 := by
  have h1 := hc n (r g) (s g)
  rw [hrs, h0 n hn _ (hr g)] at h1
  simp only [D1]
  rw [hrn n hn, hsn n hn, h0 _ (hr n) _ (s_mem hrs hr hn), map_neg]
  linear_combination (norm := abel) h1

include hc in
theorem mul_left_of_zero (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (n : G) (hn : n ∈ N) (g h : G) :
    c (n * g) h = ρ n (c g h) := by
  have h1 := hc n g h
  rw [h0 n hn, h0 n hn] at h1
  linear_combination (norm := abel) - h1

include hc in
theorem theta_mul [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (g m : G) (hm : m ∈ N) (k : G) :
    c g (m * k) = c g m + ρ (g * m * g⁻¹) (c g k) := by
  have h1 := hc g m k
  have h2 := mul_left_of_zero hc h0 (g * m * g⁻¹) (Subgroup.Normal.conj_mem ‹_› m hm g) g k
  rw [inv_mul_cancel_right] at h2
  rw [h0 m hm, map_zero, h2] at h1
  linear_combination (norm := abel) h1

include hc hrs hr hrn hsn in

theorem stepB [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (e : G → A) (he0 : ∀ g ∈ N, e g = 0)
    (he : ∀ g, ∀ n ∈ N, c g (g⁻¹ * n * g) = e g - ρ n (e g)) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => ρ (r x) (e (s x))) n g = 0 ∧ c g n - D1 ρ (fun x => ρ (r x) (e (s x))) g n = 0 := by
  have ha0 : ρ (r n) (e (s n)) = 0 := by rw [he0 _ (s_mem hrs hr hn), map_zero]
  constructor
  · simp only [D1]
    rw [hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]
    abel
  · simp only [D1]
    have hconj : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› n hn g
    have h1 : g * n = (g * n * g⁻¹) * g := by group
    have h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g))) := by
      have h3 : c g n = ρ (r g) (c (s g) n) := by
        conv_lhs => rw [← hrs g]
        exact mul_left_of_zero hc h0 _ (hr g) _ _
      have h4 := he (s g) (s g * n * (s g)⁻¹) (Subgroup.Normal.conj_mem ‹_› n hn _)
      have h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n := by group
      rw [h5] at h4
      rw [h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      have key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a := by intros; group
      have key' := key (r g) (s g)
      rw [hrs] at key'
      rw [key']
    rw [ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]
    abel

include hc in

theorem stepC [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (h0' : ∀ n ∈ N, ∀ g, c g n = 0) (n : G) (hn : n ∈ N)
    (g h : G) : c g (h * n) = c g h ∧ c (g * n) h = c g h ∧ ρ n (c g h) = c g h := by
  have hR : ∀ g h n, n ∈ N → c g (h * n) = c g h := fun g h n hn => by
    have h1 := hc g h n
    rw [h0' n hn, h0' n hn, map_zero] at h1
    linear_combination (norm := abel) h1
  have hL : ∀ g h n, n ∈ N → c g (n * h) = c g h := fun g h n hn => by
    have : n * h = h * (h⁻¹ * n * h) := by group
    rw [this, hR _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn h)]
  have hM : ∀ g h n, n ∈ N → c (g * n) h = c g h := fun g h n hn => by
    have h1 := hc g n h
    rw [h0 n hn, h0' n hn, map_zero, hL _ _ _ hn] at h1
    linear_combination (norm := abel) - h1
  refine ⟨hR g h n hn, hM g h n hn, ?_⟩
  rw [← mul_left_of_zero hc h0 n hn]
  have : n * g = g * (g⁻¹ * n * g) := by group
  rw [this, hM _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn g)]

end Alg

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
