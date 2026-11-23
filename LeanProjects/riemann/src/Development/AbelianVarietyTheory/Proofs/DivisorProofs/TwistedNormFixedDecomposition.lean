import Mathlib
open scoped Classical

namespace GlobalTheory.TwistStab

variable {H : Type} [Group H]

theorem commensurable_comap {f : H →* H} (hf : Function.Surjective f) {A B : Subgroup H}
    (h : A.Commensurable B) : (A.comap f).Commensurable (B.comap f) :=
  ⟨by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.1,
   by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.2⟩

theorem finite_cover {A B : Subgroup H} (h : A.relIndex B ≠ 0) :
    ∃ R : Finset H, (∀ f ∈ R, f ∈ B) ∧ ∀ b ∈ B, ∃ f ∈ R, ∃ a ∈ A, b = f * a := by
  haveI : (A.subgroupOf B).FiniteIndex := ⟨h⟩
  haveI : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨(Set.finite_range (fun q : B ⧸ A.subgroupOf B => ((Quotient.out q : B) : H))).toFinset,
    ?_, ?_⟩
  · intro f hf
    simp only [Set.Finite.mem_toFinset, Set.mem_range] at hf
    obtain ⟨q, rfl⟩ := hf
    exact (Quotient.out q).2
  · intro b hb
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
    refine ⟨((Quotient.out (QuotientGroup.mk (⟨b, hb⟩ : B) : B ⧸ A.subgroupOf B) : B) : H), ?_,
      ((a : B) : H)⁻¹, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨_, rfl⟩
    · exact A.inv_mem (Subgroup.mem_subgroupOf.mp a.2)
    · rw [ha]
      simp

def iterComap (T : H →* H) (K : Subgroup H) (n : ℕ) : Subgroup H :=
  (fun C : Subgroup H => C.comap T)^[n] K

theorem iterComap_succ (T : H →* H) (K : Subgroup H) (n : ℕ) :
    iterComap T K (n + 1) = (iterComap T K n).comap T :=
  Function.iterate_succ_apply' _ n K

theorem mem_iterComap (T : H →* H) (K : Subgroup H) :
    ∀ (n : ℕ) (x : H), x ∈ iterComap T K n ↔ (⇑T)^[n] x ∈ K
  | 0, _ => Iff.rfl
  | n + 1, x => by
    rw [iterComap_succ, Subgroup.mem_comap, mem_iterComap T K n, Function.iterate_succ_apply]

theorem stable_subgroup : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    ∀ Z : Subgroup H, (∀ z ∈ Z, δ * θ z * δ⁻¹ ∈ Z) → (∀ z ∈ Z, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ ((Z ⊓ K₀ : Subgroup H) : Set H))) →
    ∃ U : Subgroup H, U ≤ Z ∧ U ≤ K₀ ∧ (∀ u ∈ U, δ * θ u * δ⁻¹ ∈ U) ∧
      (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) ∧
      (∀ h g : H, ∃ F : Finset H, ∀ z ∈ Z, ∀ k ∈ K₀, z = h * k * g → ∃ f ∈ F, ∃ u ∈ U, z = f * u) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm Z hZ hZr hG
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  set T : H →* H := (MulAut.conj δ).toMonoidHom.comp θ with hT
  have hTapp : ∀ x, T x = δ * θ x * δ⁻¹ := fun x => by
    simp [T, MulAut.conj_apply]
  have hθs : Function.Surjective θ := fun y =>
    ⟨(⇑θ)^[s] y, by rw [← Function.iterate_succ_apply' (⇑θ) s y]; exact hθr y⟩
  have hTs : Function.Surjective T := fun y => by
    obtain ⟨x, hx⟩ := hθs (δ⁻¹ * y * δ)
    exact ⟨x, by rw [hTapp, hx]; group⟩
  have hθK' : ∀ n : ℕ, ∀ k ∈ K₀, (⇑θ)^[n] k ∈ K₀ := by
    intro n
    induction n with
    | zero => intro k hk; exact hk
    | succ n ih => intro k hk; rw [Function.iterate_succ_apply']; exact hθK _ (ih k hk)
  have hcθ : K₀.comap θ = K₀ := by
    ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have e : (⇑θ)^[s] (θ x) = x := by rw [← Function.iterate_succ_apply]; exact hθr x
      rw [← e]
      exact hθK' s _ hx
    · exact hθK x
  have hconj : K₀.comap (MulAut.conj δ).toMonoidHom = K₀.map (MulAut.conj δ⁻¹).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨δ * x * δ⁻¹, hx, by group⟩
    · rintro ⟨k, hk, rfl⟩
      convert hk using 1
      group
  have hTK : (K₀.comap T).Commensurable K₀ := by
    have h1 : (K₀.comap (MulAut.conj δ).toMonoidHom).Commensurable K₀ := hconj ▸ hcomm δ⁻¹
    have := commensurable_comap hθs h1
    rw [Subgroup.comap_comap, hcθ] at this
    exact this
  have hW : ∀ n, (iterComap T K₀ n).Commensurable K₀ := by
    intro n
    induction n with
    | zero => exact Subgroup.Commensurable.refl _
    | succ n ih => rw [iterComap_succ]; exact (commensurable_comap hTs ih).trans hTK
  set V : Subgroup H := ⨅ i : Fin (s + 1), iterComap T K₀ i with hV
  set U : Subgroup H := Z ⊓ V with hU
  have hfin : ∀ g : H, U.relIndex (Z ⊓ K₀.map (MulAut.conj g).toMonoidHom) ≠ 0 := by
    intro g
    apply Subgroup.relIndex_inf_ne_zero
    · rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
      exact one_ne_zero
    · apply Subgroup.relIndex_iInf_ne_zero
      intro i
      exact Subgroup.relIndex_ne_zero_trans ((hW i).trans (hcomm g).symm).1
        (by rw [Subgroup.relIndex_eq_one.mpr inf_le_right]; exact one_ne_zero)
  have hUK : U ≤ K₀ := by
    intro u hu
    have := Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hu).2 ⟨0, Nat.succ_pos s⟩
    exact this
  refine ⟨U, inf_le_left, hUK, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨huZ, huV⟩ := Subgroup.mem_inf.mp hu
    rw [← hTapp]
    refine Subgroup.mem_inf.mpr ⟨by rw [hTapp]; exact hZ u huZ, ?_⟩
    rw [Subgroup.mem_iInf]
    intro i
    rw [mem_iterComap, ← Function.iterate_succ_apply]
    show (⇑T)^[(i : ℕ) + 1] u ∈ K₀
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (s + 1) with h | h
    · have := Subgroup.mem_iInf.mp huV ⟨(i : ℕ) + 1, h⟩
      rw [mem_iterComap] at this
      exact this
    · have e : (i : ℕ) + 1 = s + 1 := by omega
      rw [e, hZr u huZ]
      exact hUK hu
  · obtain ⟨R, hRB, hR⟩ := finite_cover (hfin 1)
    obtain ⟨G, hGZ, hGcl⟩ := hG
    refine ⟨G ∪ R, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · exact hGZ g h
      · exact (Subgroup.mem_inf.mp (hRB g h)).1
    · refine hGcl.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x (hx | hx)
      · exact Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left _ hx)))
      · have hx' := Subgroup.mem_inf.mp hx
        have hx1 : x ∈ Z ⊓ K₀.map (MulAut.conj (1 : H)).toMonoidHom :=
          Subgroup.mem_inf.mpr ⟨hx'.1, ⟨x, hx'.2, by simp [MulAut.conj_apply]⟩⟩
        obtain ⟨f, hf, a, ha, rfl⟩ := hR x hx1
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right _ hf))))
          (Subgroup.subset_closure (Or.inr ha))
  · intro h g
    obtain ⟨R, -, hR⟩ := finite_cover (hfin g⁻¹)
    by_cases hex : ∃ z₀ ∈ Z, ∃ k₀ ∈ K₀, z₀ = h * k₀ * g
    · obtain ⟨z₀, hz₀, k₀, hk₀, rfl⟩ := hex
      refine ⟨R.image (fun f => h * k₀ * g * f), ?_⟩
      intro z hz k hk hzk
      have hmem : (h * k₀ * g)⁻¹ * z ∈ Z ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine Subgroup.mem_inf.mpr ⟨Z.mul_mem (Z.inv_mem hz₀) hz,
          ⟨k₀⁻¹ * k, K₀.mul_mem (K₀.inv_mem hk₀) hk, ?_⟩⟩
        rw [hzk]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      obtain ⟨f, hf, a, ha, hfa⟩ := hR _ hmem
      refine ⟨h * k₀ * g * f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, a, ha, ?_⟩
      rw [mul_assoc (h * k₀ * g) f a, ← hfa]
      group
    · exact ⟨∅, fun z hz k hk hzk => absurd ⟨z, hz, k, hk, hzk⟩ hex⟩

end GlobalTheory.TwistStab
