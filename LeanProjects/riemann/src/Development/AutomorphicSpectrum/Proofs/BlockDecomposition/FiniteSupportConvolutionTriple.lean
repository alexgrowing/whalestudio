import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

namespace GlobalTheory.CompanionTheory.HeckeProduct

section Single

variable {G M V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem out_invariant (K : Subgroup G) (F : G → M) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (g : G) :
    F ((g : G ⧸ K).out) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hh]; exact hF g h h.2

noncomputable def heckeSum (π : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (u : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out u

variable (π : Representation ℂ G V) (K : Subgroup G) {f : G → ℂ}

theorem term_support_subset (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    (Function.support fun q : G ⧸ K => f q.out • π q.out u) ⊆ hf.toFinset := by
  intro q hq
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro h0
  exact hq (by simp [h0])

theorem heckeSum_eq_sum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeSum π K f u = ∑ q ∈ hf.toFinset, f q.out • π q.out u :=
  finsum_eq_sum_of_support_subset _ (term_support_subset π K hf u)

theorem map_heckeSum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (T : V →ₗ[ℂ] V) (hT : ∀ g u, T (π g u) = π g (T u)) (u : V) :
    T (heckeSum π K f u) = heckeSum π K f (T u) := by
  rw [heckeSum_eq_sum π K hf, heckeSum_eq_sum π K hf, map_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hT]

noncomputable def heckeLin (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) : V →ₗ[ℂ] V :=
  ∑ q ∈ hf.toFinset, f q.out • π q.out

theorem heckeLin_apply (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeLin π K hf u = heckeSum π K f u := by
  rw [heckeSum_eq_sum π K hf, heckeLin, LinearMap.sum_apply]
  rfl

theorem heckeSum_fixed (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (hl : ∀ k ∈ K, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K, π k u = u) (k : G) (hk : k ∈ K) :
    π k (heckeSum π K f u) = heckeSum π K f u := by
  have hF : ∀ g, ∀ c ∈ K, (fun g => f g • π g u) (g * c) = (fun g => f g • π g u) g := by
    intro g c hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, hr c hc]
  have key : ∀ q : G ⧸ K, π k (f q.out • π q.out u)
      = (fun q : G ⧸ K => f q.out • π q.out u) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
    intro q
    have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h1 := out_invariant K (fun g => f g • π g u) hF (k * q.out)
    simp only [hq]
    rw [h1, map_smul, hl k hk, map_mul, Module.End.mul_apply]
  have h2 : π k (heckeSum π K f u) = ∑ᶠ q : G ⧸ K, π k (f q.out • π q.out u) := by
    rw [heckeSum_eq_sum π K hf, map_sum]
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro q hq
    refine term_support_subset π K hf u ?_
    intro h0
    exact hq (by simp only [h0, map_zero])
  rw [h2, finsum_congr key]
  exact finsum_comp_equiv (f := fun q : G ⧸ K => f q.out • π q.out u)
    (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

end Single

section Product

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

noncomputable def cosetPairEquiv (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) :
    (G₁ ⧸ K₁) × (G₂ ⧸ K₂) ≃ (G₁ × G₂) ⧸ K₁.prod K₂ :=
  Equiv.ofBijective (fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)) (by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' := QuotientGroup.eq.1 h
      rw [Subgroup.mem_prod] at h'
      have ha : (a.out : G₁ ⧸ K₁) = a'.out := QuotientGroup.eq.2 h'.1
      have hb : (b.out : G₂ ⧸ K₂) = b'.out := QuotientGroup.eq.2 h'.2
      simp only [QuotientGroup.out_eq'] at ha hb
      rw [ha, hb]
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        refine ⟨((g.1 : G₁ ⧸ K₁), (g.2 : G₂ ⧸ K₂)), ?_⟩
        obtain ⟨c₁, h₁⟩ := QuotientGroup.mk_out_eq_mul K₁ g.1
        obtain ⟨c₂, h₂⟩ := QuotientGroup.mk_out_eq_mul K₂ g.2
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_prod]
        simp only [h₁, h₂, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
        constructor
        · simpa using K₁.inv_mem c₁.2
        · simpa using K₂.inv_mem c₂.2)

variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)

noncomputable abbrev left : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂)

noncomputable abbrev right : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂)

theorem left_right_comm (g : G₁) (h : G₂) (u : V) :
    left ρ g (right ρ h u) = right ρ h (left ρ g u) := by
  have e1 : left ρ g (right ρ h u) = ρ ((g, 1) * (1, h)) u := by
    rw [map_mul]; rfl
  have e2 : right ρ h (left ρ g u) = ρ ((1, h) * (g, 1)) u := by
    rw [map_mul]; rfl
  rw [e1, e2]; simp

theorem left_right_mul (g : G₁) (h : G₂) (u : V) :
    ρ (g, h) u = left ρ g (right ρ h u) := by
  have : ((g, h) : G₁ × G₂) = (g, 1) * (1, h) := by simp
  rw [this, map_mul]; rfl

variable {f : G₁ → ℂ} {f' : G₂ → ℂ}

theorem sum_left_right_comm (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite) (u : V) :
    heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u)
      = heckeSum (right ρ) K₂ f' (heckeSum (left ρ) K₁ f u) := by
  rw [← heckeLin_apply (left ρ) K₁ hf, ← heckeLin_apply (left ρ) K₁ hf]
  refine map_heckeSum (right ρ) K₂ hf' _ (fun h w => ?_) u
  rw [heckeLin_apply (left ρ) K₁ hf, heckeLin_apply (left ρ) K₁ hf]
  exact map_heckeSum (left ρ) K₁ hf (right ρ h) (fun g w => (left_right_comm ρ g h w).symm) w |>.symm

theorem product_sum (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g) (hr' : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f q.out.1 * f' q.out.2) • ρ q.out u
      = heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u) := by
  have hF : ∀ g, ∀ c ∈ K₁.prod K₂, (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) (g * c)
      = (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) g := by
    intro g c hc
    have hc' := Subgroup.mem_prod.1 hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, Prod.fst_mul, Prod.snd_mul,
      hr c.1 hc'.1, hr' c.2 hc'.2]
  rw [← finsum_comp_equiv (cosetPairEquiv K₁ K₂)]
  have h1 : ∀ p : (G₁ ⧸ K₁) × (G₂ ⧸ K₂),
      (f ((cosetPairEquiv K₁ K₂ p).out.1) * f' ((cosetPairEquiv K₁ K₂ p).out.2)) •
        ρ (cosetPairEquiv K₁ K₂ p).out u = (f p.1.out * f' p.2.out) • ρ (p.1.out, p.2.out) u :=
    fun p => out_invariant (K₁.prod K₂) (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) hF
      (p.1.out, p.2.out)
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ hf'.toFinset) _ ?_,
    Finset.sum_product, heckeSum_eq_sum _ K₁ hf]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [heckeSum_eq_sum _ K₂ hf', map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [left_right_mul, map_smul, smul_smul]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.coe_product, Set.Finite.coe_toFinset, Set.mem_prod, Function.mem_support]
    constructor
    · intro h0; exact hp (by simp [h0])
    · intro h0; exact hp (by simp [h0])

theorem fixed_left (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hl : ∀ k ∈ K₁, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (left ρ) K₁ f u) = heckeSum (left ρ) K₁ f u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : ∀ k ∈ K₁, left ρ k u = u := fun k hk =>
    hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  have hu₂ : right ρ c₂ u = u := hu (1, c₂) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hc'.2⟩)
  rw [left_right_mul, map_heckeSum (left ρ) K₁ hf (right ρ c₂)
    (fun g w => (left_right_comm ρ g c₂ w).symm), hu₂]
  exact heckeSum_fixed (left ρ) K₁ hf hl hr u hu₁ c₁ hc'.1

theorem fixed_right (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hl : ∀ k ∈ K₂, ∀ g, f' (k * g) = f' g) (hr : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (right ρ) K₂ f' u) = heckeSum (right ρ) K₂ f' u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : left ρ c₁ u = u := hu (c₁, 1) (Subgroup.mem_prod.2 ⟨hc'.1, K₂.one_mem⟩)
  have hu₂ : ∀ k ∈ K₂, right ρ k u = u := fun k hk =>
    hu (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  rw [left_right_mul, heckeSum_fixed (right ρ) K₂ hf' hl hr u hu₂ c₂ hc'.2,
    map_heckeSum (right ρ) K₂ hf' (left ρ c₁) (fun h w => left_right_comm ρ c₁ h w), hu₁]

end Product

theorem product_operators_mul : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  intro G₁ G₂ V _ _ _ _ ρ K₁ K₂ f₁ f₁' f₁'' f₂ f₂' f₂'' h1 h2 hA hB v hv
  obtain ⟨a, ai⟩ := h1 f₁ (by simp)
  obtain ⟨a', ai'⟩ := h1 f₁' (by simp)
  obtain ⟨a'', ai''⟩ := h1 f₁'' (by simp)
  obtain ⟨b, bi⟩ := h2 f₂ (by simp)
  obtain ⟨b', bi'⟩ := h2 f₂' (by simp)
  obtain ⟨b'', bi''⟩ := h2 f₂'' (by simp)
  have hA' : ∀ w : V, (∀ k ∈ K₁, left ρ k w = w) → heckeSum (left ρ) K₁ f₁'' w
      = heckeSum (left ρ) K₁ f₁ (heckeSum (left ρ) K₁ f₁' w) := hA
  have hB' : ∀ w : V, (∀ k ∈ K₂, right ρ k w = w) → heckeSum (right ρ) K₂ f₂'' w
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' w) := hB
  have hv₂ : ∀ k ∈ K₂, right ρ k v = v := fun k hk =>
    hv (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  have hy := fixed_right ρ K₁ K₂ b' (fun k hk g => (bi' k hk g).1) (fun k hk g => (bi' k hk g).2) v hv
  have hx := fixed_right ρ K₁ K₂ b (fun k hk g => (bi k hk g).1) (fun k hk g => (bi k hk g).2) _ hy
  have hw := fixed_left ρ K₁ K₂ a' (fun k hk g => (ai' k hk g).1) (fun k hk g => (ai' k hk g).2) _ hy
  have hx₁ : ∀ k ∈ K₁, left ρ k (heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v))
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v) := fun k hk =>
    hx (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  rw [product_sum ρ K₁ K₂ a'' b'' (fun k hk g => (ai'' k hk g).2) (fun k hk g => (bi'' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a' b' (fun k hk g => (ai' k hk g).2) (fun k hk g => (bi' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a b (fun k hk g => (ai k hk g).2) (fun k hk g => (bi k hk g).2) _ hw,
    hB' v hv₂, hA' _ hx₁, sum_left_right_comm ρ K₁ K₂ a' b]

end GlobalTheory.CompanionTheory.HeckeProduct
