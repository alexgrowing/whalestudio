import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.Ord2.OpenInv

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {n : ℕ} {a b c : Qbar l} (h1 : Cg n a b) (h2 : Cg n b c) : Cg n a c := by
  unfold Cg at *
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖a - b‖ ‖b - c‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_symm {n : ℕ} {a b : Qbar l} (h1 : Cg n a b) : Cg n b a := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_refl {n : ℕ} (a : Qbar l) : Cg n a a := by
  unfold Cg
  rw [sub_self, norm_zero]
  exact norm_nonneg _

private theorem eps_eq_algebraMap_cycZ (s : G ℚ Ω) :
    eps l s = algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
  unfold eps cycBar
  rfl

theorem norm_eps_le (s : G ℚ Ω) : ‖eps l s‖ ≤ 1 := by
  rw [eps_eq_algebraMap_cycZ]
  unfold Qbar
  rw [PadicAlgCl.norm_extends]
  exact (ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]).2

theorem cg_mul_eps {n : ℕ} (s : G ℚ Ω) {a b : Qbar l} (h : Cg n a b) : Cg n (eps l s * a) (eps l s * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖eps l s‖ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right (norm_eps_le s) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

theorem eps_mul (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by
  unfold eps
  rw [map_mul, Units.val_mul]

theorem eps_one : eps l (1 : G ℚ Ω) = 1 := by
  unfold eps
  rw [map_one, Units.val_one]

theorem pow_pos' (n : ℕ) : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ :=
  norm_pos_iff.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))

private theorem continuous_eps' : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : (fun s : G ℚ Ω => eps l s) =
      fun s => algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
    funext s
    exact eps_eq_algebraMap_cycZ s
  rw [h]
  have h1 : Continuous fun s : G ℚ Ω => ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (ReciprocityTheory.Gal.continuous_cycZ ℚ Ω l)
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (h2.comp h1)

theorem ev_cg {X : Type} [TopologicalSpace X] {n : ℕ} {f g : X → Qbar l} (hf : Continuous f) (hg : Continuous g)
    {x : X} (h : f x = g x) : ∀ᶠ y in 𝓝 x, Cg n (f y) (g y) := by
  have hc : Continuous fun y => ‖f y - g y‖ := (hf.sub hg).norm
  have h0 : ‖f x - g x‖ < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [h, sub_self, norm_zero]
    exact pow_pos' n
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with y hy
  unfold Cg
  exact hy.le

def invSub (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) : Subgroup (G ℚ Ω) where
  carrier := {k | k ∈ H ∧ Cg n (eps l k) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)}
  one_mem' := ⟨H.one_mem, by rw [eps_one]; exact cg_refl _, fun s _ t _ => by
    rw [mul_one, mul_one]; exact ⟨cg_refl _, cg_refl _⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨H.mul_mem ha hb, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · rw [eps_mul]
      have := cg_mul_eps a hb1
      rw [mul_one] at this
      exact cg_trans this ha1
    · rw [← mul_assoc]
      exact cg_trans (hb2 _ (H.mul_mem hs ha) t ht).1 (ha2 s hs t ht).1
    · rw [← mul_assoc]
      exact cg_trans (hb2 s hs _ (H.mul_mem ht ha)).2 (ha2 s hs t ht).2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨H.inv_mem ha, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · have := cg_mul_eps a⁻¹ ha1
      rw [mul_one, ← eps_mul, inv_mul_cancel, eps_one] at this
      exact cg_symm this
    · have := (ha2 _ (H.mul_mem hs (H.inv_mem ha)) t ht).1
      rw [inv_mul_cancel_right] at this
      exact cg_symm this
    · have := (ha2 s hs _ (H.mul_mem ht (H.inv_mem ha))).2
      rw [inv_mul_cancel_right] at this
      exact cg_symm this

theorem open_inv : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (H I : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), IsClosed (H : Set (G ℚ Ω)) → I ≤ H → ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2) ((H : Set (G ℚ Ω)) ×ˢ (H : Set (G ℚ Ω))) → (∀ i ∈ I, eps l i = 1) → (∀ s ∈ H, ∀ t ∈ H, ∀ i ∈ I, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)) → ∃ K : Subgroup (G ℚ Ω), I ≤ K ∧ K ≤ H ∧ IsOpen ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧ (∀ k ∈ K, Cg n (eps l k) 1) ∧ ∀ s ∈ H, ∀ t ∈ H, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t) := by
  intro l _ Ω _ _ _ n H I ξ hH hIH hξ hI hinv
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  have hξc : Continuous fun p : H × H => ξ p.1 p.2 := by
    have hp : Continuous fun p : H × H => ((p.1 : G ℚ Ω), (p.2 : G ℚ Ω)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    exact hξ.comp_continuous hp (fun p => ⟨p.1.2, p.2.2⟩)
  have hL : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ ((y.1 * k : H) : G ℚ Ω) y.2) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ ((z.2.1 * z.1 : H) : G ℚ Ω) z.2.2) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp ((continuous_snd.fst.mul continuous_fst).prodMk continuous_snd.snd))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hR : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ y.1 ((y.2 * k : H) : G ℚ Ω)) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ z.2.1 ((z.2.2 * z.1 : H) : G ℚ Ω)) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp (continuous_snd.fst.prodMk (continuous_snd.snd.mul continuous_fst)))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hE : ∀ᶠ k : H in 𝓝 (1 : H), Cg n (eps l (k : G ℚ Ω)) 1 := by
    refine ev_cg (X := H) (n := n) (f := fun k => eps l (k : G ℚ Ω)) (g := fun _ => 1)
      (continuous_eps'.comp continuous_subtype_val) continuous_const ?_
    show eps l ((1 : H) : G ℚ Ω) = 1
    rw [OneMemClass.coe_one, eps_one]
  refine ⟨invSub n H ξ, ?_, fun k hk => hk.1, ?_, fun k hk => hk.2.1, fun s hs t ht k hk => hk.2.2 s hs t ht⟩
  · intro i hi
    have hiH : i ∈ H := hIH hi
    show i ∈ H ∧ Cg n (eps l i) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)
    refine ⟨hiH, ?_, fun s hs t ht => hinv s hs t ht i hi⟩
    rw [hI i hi]
    exact cg_refl _
  · apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hL, hR, hE] with k hkL hkR hkE
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    show (k : G ℚ Ω) ∈ H ∧ Cg n (eps l (k : G ℚ Ω)) 1 ∧ ∀ s ∈ H, ∀ t ∈ H,
      Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)
    exact ⟨k.2, hkE, fun s hs t ht => ⟨hkL (⟨s, hs⟩, ⟨t, ht⟩) trivial, hkR (⟨s, hs⟩, ⟨t, ht⟩) trivial⟩⟩

end GlobalTheory.Ord2.OpenInv

end
