import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Classical

namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {G : Type} [Group G]

theorem mem_dc_iff (K : Subgroup G) (g x : G) :
    x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      ∃ a : K, ∃ b : K, x = (a : G) * g * b := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩

theorem mem_dc_one (K : Subgroup G) (x : G) :
    x ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ x ∈ K := by
  rw [mem_dc_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    rw [mul_one]
    exact K.mul_mem a.2 b.2
  · intro hx
    exact ⟨⟨x, hx⟩, 1, by simp⟩

theorem ind_biInv (k : Type) [CommRing k] (K : Subgroup G) (T : Set G)
    (hT : ∀ a b : K, ∀ x : G, x ∈ T → (a : G) * x * b ∈ T) :
    IsBiInv K (T.indicator (1 : G → k)) := by
  unfold IsBiInv
  intro a b x
  by_cases hx : x ∈ T
  · simp [Set.indicator_apply, hx, hT a b x hx]
  · have h' : (a : G) * x * b ∉ T := by
      intro h
      apply hx
      have := hT a⁻¹ b⁻¹ _ h
      simpa [mul_assoc] using this
    simp [Set.indicator_apply, hx, h']

theorem dc_stable (K : Subgroup G) (g : G) (a b : K) (x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) :
    (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [mem_dc_iff] at hx ⊢
  obtain ⟨c, d, rfl⟩ := hx
  exact ⟨a * c, d * b, by simp [mul_assoc]⟩

theorem mem_hecke_iff (k : Type) [CommRing k] (K : Subgroup G) (f : G → k) :
    f ∈ Hecke k K ↔ IsBiInv K f ∧ FinDosetSupp K f := Iff.rfl

theorem dosetInd_of_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 1 := by
  simp [dosetInd, hx]

theorem dosetInd_of_not_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∉ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 0 := by
  simp [dosetInd, hx]

theorem out_mem_of_eq_one (K : Subgroup G) (x : G ⧸ K) (hx : x = ((1 : G) : G ⧸ K)) :
    x.out ∈ K := by
  have h : ((x.out : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by rw [QuotientGroup.out_eq', hx]
  rw [QuotientGroup.eq] at h
  simpa using h

theorem out_not_mem_of_ne_one (K : Subgroup G) (x : G ⧸ K) (hx : x ≠ ((1 : G) : G ⧸ K)) :
    x.out ∉ K := by
  intro h
  apply hx
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  simpa using h

end Generic

theorem double_coset_indicator_mem : Formalism.UG.DosetIndMem := by
  unfold Formalism.UG.DosetIndMem
  intro G _ K k _ g
  rw [mem_hecke_iff]
  refine ⟨ind_biInv k K _ (fun a b x hx => dc_stable K g a b x hx), ?_⟩
  refine ⟨{g}, fun x hx => ⟨g, Finset.mem_singleton_self g, (mem_dc_iff K g x).1 ?_⟩⟩
  by_contra h
  exact hx (dosetInd_of_not_mem k K g x h)

theorem hecke_algebra_unit : Formalism.UG.HeckeUnit := by
  unfold Formalism.UG.HeckeUnit
  intro G _ K k _ f hf
  unfold conv
  have hb := ((mem_hecke_iff k K f).1 hf).1
  have h1 : ∀ y : G, dosetInd k K 1 y = if y ∈ K then 1 else 0 := by
    intro y
    by_cases hy : y ∈ K
    · rw [if_pos hy, dosetInd_of_mem]
      exact (mem_dc_one K y).2 hy
    · rw [if_neg hy, dosetInd_of_not_mem]
      exact fun h => hy ((mem_dc_one K y).1 h)
  refine ⟨funext fun g => ?_, funext fun g => ?_⟩
  · show ∑ᶠ x : G ⧸ K, dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g) = f g
    have e := finsum_eq_single
      (fun x : G ⧸ K => dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g))
      ((1 : G) : G ⧸ K) (fun x hx => by
        show dosetInd k K 1 (Quotient.out x) * f ((Quotient.out x)⁻¹ * g) = 0
        rw [h1, if_neg (out_not_mem_of_ne_one K x hx), zero_mul])
    rw [e]
    have hm := out_mem_of_eq_one K ((1 : G) : G ⧸ K) rfl
    rw [h1, if_pos hm, one_mul]
    have := hb ⟨(Quotient.out ((1 : G) : G ⧸ K))⁻¹, K.inv_mem hm⟩ 1 g
    simpa using this
  · show ∑ᶠ x : G ⧸ K, f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g) = f g
    have e := finsum_eq_single
      (fun x : G ⧸ K => f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g))
      ((g : G) : G ⧸ K) (fun x hx => by
        show f (Quotient.out x) * dosetInd k K 1 ((Quotient.out x)⁻¹ * g) = 0
        have hm : (Quotient.out x)⁻¹ * g ∉ K := by
          intro h
          apply hx
          rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
          exact h
        rw [h1, if_neg hm, mul_zero])
    rw [e]
    have hm : (Quotient.out ((g : G) : G ⧸ K))⁻¹ * g ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [h1, if_pos hm, mul_one]
    have := (hb 1 ⟨(Quotient.out ((g : G) : G ⧸ K))⁻¹ * g, hm⟩ (Quotient.out ((g : G) : G ⧸ K))).symm
    simpa using this

theorem hecke_action_identity : Formalism.UG.HeckeActOne := by
  unfold Formalism.UG.HeckeActOne
  intro G _ Γ K k _ W _ _ ρ φ hφ
  unfold hAct
  have h1 : ∀ y : G, dosetInd k K 1 y = if y ∈ K then 1 else 0 := by
    intro y
    by_cases hy : y ∈ K
    · rw [if_pos hy, dosetInd_of_mem]
      exact (mem_dc_one K y).2 hy
    · rw [if_neg hy, dosetInd_of_not_mem]
      exact fun h => hy ((mem_dc_one K y).1 h)
  refine funext fun g => ?_
  show ∑ᶠ x : G ⧸ K, dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x) = φ g
  have e := finsum_eq_single
    (fun x : G ⧸ K => dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x))
    ((1 : G) : G ⧸ K) (fun x hx => by
      show dosetInd k K 1 (Quotient.out x) • φ (g * Quotient.out x) = 0
      rw [h1, if_neg (out_not_mem_of_ne_one K x hx), zero_smul])
  rw [e]
  have hm := out_mem_of_eq_one K ((1 : G) : G ⧸ K) rfl
  rw [h1, if_pos hm, one_smul]
  simp [AMF] at hφ
  have := hφ 1 Γ.one_mem g _ hm
  rw [one_mul, show (⟨1, Γ.one_mem⟩ : Γ) = 1 from rfl, map_one] at this
  simpa using this

section Basis

variable {G : Type} [Group G]

theorem mk_out_dc (K : Subgroup G) (g : G) :
    ∃ a b : K, Quotient.out (DoubleCoset.mk K K g) = (a : G) * g * b := by
  obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).1
    (DoubleCoset.out_eq' K K _).symm
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

theorem biInv_mk_out {k : Type} (K : Subgroup G) (f : G → k) (hf : IsBiInv K f) (g : G) :
    f (Quotient.out (DoubleCoset.mk K K g)) = f g := by
  obtain ⟨a, b, e⟩ := mk_out_dc K g
  rw [e]
  exact hf a b g

def toFs (k : Type) [CommRing k] (K : Subgroup G) (f : Hecke k K) : ClassSet K K →₀ k :=
  Finsupp.ofSupportFinite (fun c => (f : G → k) (Quotient.out c)) (by
    obtain ⟨S, hS⟩ := f.2.2
    refine (S.finite_toSet.image (DoubleCoset.mk K K)).subset ?_
    intro c hc
    obtain ⟨s, hs, a, b, e⟩ := hS (Quotient.out c) hc
    exact ⟨s, hs, ((DoubleCoset.eq K K s (Quotient.out c)).2 ⟨a, a.2, b, b.2, e⟩).trans
      (DoubleCoset.out_eq' K K c)⟩)

theorem toFs_apply (k : Type) [CommRing k] (K : Subgroup G) (f : Hecke k K) (c : ClassSet K K) :
    toFs k K f c = (f : G → k) (Quotient.out c) := rfl

def ofFs (k : Type) [CommRing k] (K : Subgroup G) (c : ClassSet K K →₀ k) : Hecke k K :=
  ⟨fun g => c (DoubleCoset.mk K K g), by
    refine ⟨fun a b g => ?_, ?_⟩
    · exact congrArg c ((DoubleCoset.eq K K g ((a : G) * g * b)).2 ⟨a, a.2, b, b.2, rfl⟩).symm
    · refine ⟨c.support.image Quotient.out, fun g hg => ?_⟩
      refine ⟨Quotient.out (DoubleCoset.mk K K g),
        Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), ?_⟩
      obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq K K (Quotient.out (DoubleCoset.mk K K g)) g).1
        (DoubleCoset.out_eq' K K (DoubleCoset.mk K K g))
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

end Basis

def heckeEquiv {G : Type} [Group G] (K : Subgroup G) (k : Type) [CommRing k] :
    Hecke k K ≃ₗ[k] (ClassSet K K →₀ k) where
  toFun := toFs k K
  invFun := ofFs k K
  map_add' f f' := by
    ext c
    simp only [toFs_apply, Finsupp.add_apply, Submodule.coe_add, Pi.add_apply]
  map_smul' r f := by
    ext c
    simp only [toFs_apply, Finsupp.smul_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv f := by
    apply Subtype.ext
    funext g
    exact biInv_mk_out K _ f.2.1 g
  right_inv c := by
    ext d
    show c (DoubleCoset.mk K K (Quotient.out d)) = c d
    rw [DoubleCoset.out_eq']

theorem hecke_algebra_basis : Formalism.UG.HeckeBasis := by
  unfold Formalism.UG.HeckeBasis
  intro G _ K k _
  exact ⟨heckeEquiv K k, fun f g => biInv_mk_out K _ f.2.1 g⟩

theorem Tj_double_coset_mem : Formalism.UG.TjMem := by
  unfold Formalism.UG.TjMem
  intro L _ O ϖ k _ n j hϖ
  rw [mem_hecke_iff]
  constructor
  · unfold Tj
    apply ind_biInv
    rintro a' b' x ⟨a, ha, b, hb, e⟩
    rw [Set.mem_setOf_eq]
    exact ⟨↑a' * a, (GLint (Fin n) O).mul_mem a'.2 ha, b * ↑b', (GLint (Fin n) O).mul_mem hb b'.2,
      by simp only [Units.val_mul, e, mul_assoc]⟩
  · by_cases hne : ∃ g0, Tj k n O ϖ j g0 ≠ 0
    · obtain ⟨g0, hg0⟩ := hne
      unfold Tj at hg0
      obtain ⟨a0, ha0, b0, hb0, e0⟩ := Set.mem_of_indicator_ne_zero hg0
      refine ⟨{g0}, fun x hx => ⟨g0, Finset.mem_singleton_self _, ?_⟩⟩
      unfold Tj at hx
      obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hx
      refine ⟨⟨a * a0⁻¹, (GLint (Fin n) O).mul_mem ha ((GLint (Fin n) O).inv_mem ha0)⟩,
        ⟨b0⁻¹ * b, (GLint (Fin n) O).mul_mem ((GLint (Fin n) O).inv_mem hb0) hb⟩, ?_⟩
      apply Units.ext
      simp only [Subgroup.coe_mk, Units.val_mul, e, e0]
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
    · push_neg at hne
      exact ⟨∅, fun x hx => absurd (hne x) hx⟩

end Formalism.UG.P
