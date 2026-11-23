import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem length_eq_ker_add_range {A : Type*} [Ring A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    length A M = length A (LinearMap.ker φ) + length A (LinearMap.range φ) := by
  exact Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])

theorem length_eq_sub_add_quot {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (P : Submodule A M) : length A M = length A P + length A (M ⧸ P) :=
  Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ P)

theorem length_eq_range_add_range {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ψ : L →ₗ[A] M} {φ : M →ₗ[A] N} (h : Function.Exact ψ φ) :
    length A M = length A (LinearMap.range ψ) + length A (LinearMap.range φ) := by
  rw [length_eq_ker_add_range φ, h.linearMap_ker_eq]

theorem length_six_term {A : Type*} [Ring A] {M₁ M₂ M₃ M₄ M₅ M₆ : Type*}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M₃] [Module A M₃] [AddCommGroup M₄] [Module A M₄]
    [AddCommGroup M₅] [Module A M₅] [AddCommGroup M₆] [Module A M₆]
    {f₁ : M₁ →ₗ[A] M₂} {f₂ : M₂ →ₗ[A] M₃} {f₃ : M₃ →ₗ[A] M₄} {f₄ : M₄ →ₗ[A] M₅}
    {f₅ : M₅ →ₗ[A] M₆} (h₁ : Function.Injective f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) (h₄ : Function.Exact f₃ f₄) (h₅ : Function.Exact f₄ f₅)
    (h₆ : Function.Surjective f₅) :
    length A M₁ + length A M₃ + length A M₅ = length A M₂ + length A M₄ + length A M₆ := by
  have e1 : length A M₁ = length A (LinearMap.range f₁) := (LinearEquiv.ofInjective f₁ h₁).length_eq
  have e6 : length A (LinearMap.range f₅) = length A M₆ :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 h₆)).length_eq
  rw [e1, length_eq_range_add_range h₂, length_eq_range_add_range h₃, length_eq_range_add_range h₄,
    length_eq_range_add_range h₅, ← e6]
  ring

def kerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    LinearMap.ker (LinearMap.lsmul A M x) →ₗ[A] LinearMap.ker (LinearMap.lsmul A N x) :=
  f.restrict (fun m hm => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm ⊢
    rw [← map_smul, hm, map_zero])

def cokerSmulMap {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) →ₗ[A]
      (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨m, rfl⟩
    exact ⟨f m, by simp⟩)

theorem euler_ses {A : Type*} [CommRing A] {M' M M'' : Type*} [AddCommGroup M'] [Module A M']
    [AddCommGroup M] [Module A M] [AddCommGroup M''] [Module A M'']
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'') (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (x : A) :
    length A (LinearMap.ker (LinearMap.lsmul A M' x)) + length A (LinearMap.ker (LinearMap.lsmul A M'' x)) +
        length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        length A (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)) +
        length A (M'' ⧸ LinearMap.range (LinearMap.lsmul A M'' x)) := by
  have key : ∀ z : LinearMap.ker (LinearMap.lsmul A M'' x), ∃ (m : M) (m' : M'),
      g m = (z : M'') ∧ f m' = x • m := by
    intro z
    obtain ⟨m, hm⟩ := hg z
    have hz : x • (z : M'') = 0 := z.2
    obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hz])
    exact ⟨m, m', hm, hm'⟩
  have indep : ∀ (m₁ : M) (m₁' : M') (m₂ : M) (m₂' : M'), g m₁ = g m₂ → f m₁' = x • m₁ →
      f m₂' = x • m₂ →
      Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₁' =
        Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m₂' := by
    intro m₁ m₁' m₂ m₂' h h1 h2
    obtain ⟨n, hn⟩ := (hex (m₁ - m₂)).1 (by rw [map_sub, h, sub_self])
    have e : m₁' - m₂' = x • n := hf (by rw [map_sub, map_smul, hn, h1, h2, smul_sub])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e]
    exact ⟨n, rfl⟩
  choose lift liftP hlift using key
  obtain ⟨δ, hδ⟩ : ∃ δ : LinearMap.ker (LinearMap.lsmul A M'' x) →ₗ[A]
      (M' ⧸ LinearMap.range (LinearMap.lsmul A M' x)),
      ∀ (z : LinearMap.ker (LinearMap.lsmul A M'' x)) (m : M) (m' : M'), g m = (z : M'') → f m' = x • m →
        δ z = Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) m' := by
    refine ⟨{ toFun := fun z => Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M' x)) (liftP z),
              map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro z₁ z₂
      show Submodule.mkQ _ (liftP (z₁ + z₂)) = Submodule.mkQ _ (liftP z₁) + Submodule.mkQ _ (liftP z₂)
      rw [← map_add]
      exact indep _ _ (lift z₁ + lift z₂) _
        (by rw [(hlift _).1, map_add, (hlift z₁).1, (hlift z₂).1, Submodule.coe_add]) (hlift _).2
        (by rw [map_add, (hlift z₁).2, (hlift z₂).2, smul_add])
    · intro a z
      show Submodule.mkQ _ (liftP (a • z)) = a • Submodule.mkQ _ (liftP z)
      rw [← map_smul]
      exact indep _ _ (a • lift z) _
        (by rw [(hlift _).1, map_smul, (hlift z).1, Submodule.coe_smul]) (hlift _).2
        (by rw [map_smul, (hlift z).2, smul_comm])
    · intro z m m' h h'
      exact indep _ _ m m' (by rw [(hlift z).1, h]) (hlift z).2 h'
  have h₁ : Function.Injective (kerSmulMap f x) := by
    intro a b h
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val h
  have h₂ : Function.Exact (kerSmulMap f x) (kerSmulMap g x) := by
    intro y
    constructor
    · intro hy
      have hy0 : g y = 0 := congrArg Subtype.val hy
      obtain ⟨m', hm'⟩ := (hex y).1 hy0
      have hyx : x • (y : M) = 0 := y.2
      refine ⟨⟨m', ?_⟩, Subtype.ext hm'⟩
      show x • m' = 0
      apply hf
      rw [map_smul, hm', hyx, map_zero]
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨w, rfl⟩
  have h₃ : Function.Exact (kerSmulMap g x) δ := by
    intro z
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨m', hm'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [hδ z m m' hm hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨n, hn⟩ := LinearMap.mem_range.1 hz
      have hn' : x • n = m' := hn
      refine ⟨⟨m - f n, ?_⟩, Subtype.ext ?_⟩
      · show x • (m - f n) = 0
        rw [smul_sub, ← map_smul, hn', hm', sub_self]
      · show g (m - f n) = z
        rw [map_sub, hm, (hex _).2 ⟨n, rfl⟩, sub_zero]
    · rintro ⟨y, rfl⟩
      have hyx : x • (y : M) = 0 := y.2
      rw [hδ _ y 0 rfl (by rw [map_zero, hyx]), map_zero]
  have h₄ : Function.Exact δ (cokerSmulMap f x) := by
    intro w
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m = f m' := hm
      refine ⟨⟨g m, ?_⟩, hδ _ m m' rfl hm2.symm⟩
      show x • g m = 0
      rw [← map_smul, hm2]
      exact (hex _).2 ⟨m', rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨m, hm⟩ := hg z
      have hzx : x • (z : M'') = 0 := z.2
      obtain ⟨n', hn'⟩ := (hex (x • m)).1 (by rw [map_smul, hm, hzx])
      rw [← hz, hδ z m n' hm hn']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f n') = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hn']
      exact ⟨m, rfl⟩
  have h₅ : Function.Exact (cokerSmulMap f x) (cokerSmulMap g x) := by
    intro w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ w
    constructor
    · intro hw
      have hw' : Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g m) = 0 := hw
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw'
      obtain ⟨m'', hm''⟩ := LinearMap.mem_range.1 hw'
      have hm2 : x • m'' = g m := hm''
      obtain ⟨t, ht⟩ := hg m''
      obtain ⟨m', hm'⟩ := (hex (m - x • t)).1 (by rw [map_sub, map_smul, ht, hm2, sub_self])
      refine ⟨Submodule.mkQ _ m', ?_⟩
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M x)) (f m') = Submodule.mkQ _ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hm']
      refine ⟨-t, ?_⟩
      show x • -t = m - x • t - m
      rw [smul_neg]
      abel
    · rintro ⟨w', hw'⟩
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w'
      rw [← hw']
      show Submodule.mkQ (LinearMap.range (LinearMap.lsmul A M'' x)) (g (f m')) = 0
      rw [(hex _).2 ⟨m', rfl⟩, map_zero]
  have h₆ : Function.Surjective (cokerSmulMap g x) := by
    intro w
    obtain ⟨m'', rfl⟩ := Submodule.mkQ_surjective _ w
    obtain ⟨m, rfl⟩ := hg m''
    exact ⟨Submodule.mkQ _ m, rfl⟩
  exact length_six_term h₁ h₂ h₃ h₄ h₅ h₆

theorem euler_finLength {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : length A N ≠ ⊤) (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (LinearMap.ker (LinearMap.lsmul A N x)) := by
  have h1 := length_eq_ker_add_range (LinearMap.lsmul A N x)
  have h2 := length_eq_sub_add_quot (LinearMap.range (LinearMap.lsmul A N x))
  have hle : length A (LinearMap.range (LinearMap.lsmul A N x)) ≤ length A N := by
    rw [h1]
    exact le_add_self
  have hR := ne_top_of_le_ne_top hN hle
  rw [h1, add_comm] at h2
  exact (WithTop.add_left_cancel hR h2).symm

end ReciprocityTheory.ChartRestriction.G.AI
