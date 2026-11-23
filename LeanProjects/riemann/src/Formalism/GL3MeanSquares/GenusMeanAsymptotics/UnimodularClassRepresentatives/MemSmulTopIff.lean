import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotInfNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomCongr
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace DA

theorem one_app (x : V) : (1 : V ≃ₗ[K] V) x = x := rfl

theorem apply_mem_smul {g : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hg : Formalism.HermitianLatticesTheory.gmap g A = A)
    (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ (I • A : Submodule (𝓞 K) V)) :
    g z ∈ (I • A : Submodule (𝓞 K) V) := by
  have h1 : g z ∈ (I • A : Submodule (𝓞 K) V).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    Submodule.mem_map_of_mem hz
  rw [Submodule.map_smul''] at h1
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg
  rwa [h2] at h1

theorem apply_mem {g : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hg : Formalism.HermitianLatticesTheory.gmap g A = A)
    {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h1 : g z ∈ A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg
  rwa [h2] at h1

theorem mem_smul_top_iff (A : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (w : ↥A) :
    w ∈ (I • ⊤ : Submodule (𝓞 K) ↥A) ↔ (w : V) ∈ (I • A : Submodule (𝓞 K) V) := by
  have e : (I • ⊤ : Submodule (𝓞 K) ↥A).map A.subtype = I • A := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← e]
  constructor
  · intro hw
    exact Submodule.mem_map_of_mem hw
  · rintro ⟨w', hw', e'⟩
    rwa [← Subtype.ext (a1 := w') (a2 := w) e']

end DA

def stabB (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ autSub h A ∧ g x - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (a * b) x - x = a (b x - x) + (a x - x) := by
      rw [LinearEquiv.mul_apply, map_sub]
      abel
    rw [e]
    exact add_mem (DA.apply_mem_smul ha.2 _ hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : a⁻¹ x - x = -(a⁻¹ (a x - x)) := by
      rw [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app]
      abel
    rw [e]
    exact neg_mem (DA.apply_mem_smul (inv_mem ha).2 _ ha')

theorem mem_stabB {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x : V}
    {g : V ≃ₗ[K] V} : g ∈ stabB h A 𝔭 J x ↔
      g ∈ autSub h A ∧ g x - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := Iff.rfl

theorem mem_tube_bot {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x y : V} :
    y ∈ tube ⊥ A 𝔭 J x ↔ y - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  constructor
  · rintro ⟨g, hg, hy⟩
    rw [Subgroup.mem_bot] at hg
    rwa [hg, DA.one_app] at hy
  · intro hy
    exact ⟨1, one_mem _, by rwa [DA.one_app]⟩

theorem quot_eq_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x : V}
    {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h A) (a b : ↥D) :
    (QuotientGroup.mk a : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) = QuotientGroup.mk b ↔
      (b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_stabB]
  have ha := hD a.2
  have hb := hD b.2
  have e1 : ((a⁻¹ * b : ↥D) : V ≃ₗ[K] V) x - x =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x) := by
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, inv_mul_cancel,
      DA.one_app]
    rfl
  constructor
  · rintro ⟨-, h2⟩
    rw [e1] at h2
    have := DA.apply_mem_smul ha.2 _ h2
    rwa [← LinearEquiv.mul_apply, mul_inv_cancel, DA.one_app] at this
  · intro h2
    refine ⟨hD (a⁻¹ * b).2, ?_⟩
    rw [e1]
    exact DA.apply_mem_smul (inv_mem ha).2 _ h2

theorem cnt_tube_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (n : 𝓞 F) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    {J k : ℕ} (hJk : J ≤ k) {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h (locF 𝔭 A₀)) :
    cnt h (locF 𝔭 A₀) 𝔭 k n (tube D (locF 𝔭 A₀) 𝔭 J x) =
      (stabB h (locF 𝔭 A₀) 𝔭 J x).relIndex D * cnt h (locF 𝔭 A₀) 𝔭 k n (tube ⊥ (locF 𝔭 A₀) 𝔭 J x) := by
  classical
  set A := locF 𝔭 A₀ with hA
  have hfinJ : Finite (↥A ⧸ ((extP K 𝔭) ^ J • ⊤ : Submodule (𝓞 K) ↥A)) := finite_quot hA₀ h𝔭 J
  have hfink : Finite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) := finite_quot hA₀ h𝔭 k

  let φ : ↥D → ↥A ⧸ ((extP K 𝔭) ^ J • ⊤ : Submodule (𝓞 K) ↥A) := fun g =>
    Submodule.Quotient.mk ⟨(g : V ≃ₗ[K] V) x, DA.apply_mem (hD g.2).2 hxA⟩
  have hφ : ∀ a b : ↥D, φ a = φ b ↔
      (QuotientGroup.mk a : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) = QuotientGroup.mk b := by
    intro a b
    rw [quot_eq_iff hD, eq_comm, Submodule.Quotient.eq, DA.mem_smul_top_iff]
    rfl
  have hfinQ : Finite (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) := by
    refine Finite.of_injective (Quotient.lift φ ?_) ?_
    · intro a b hab
      exact (hφ a b).mpr (Quotient.sound hab)
    · intro a b
      induction a using Quotient.inductionOn with | _ a => ?_
      induction b using Quotient.inductionOn with | _ b => ?_
      intro e
      exact (hφ a b).mp e
  have := Fintype.ofFinite (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D)
  let Ω : (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) → Set V := fun c =>
    tube ⊥ A 𝔭 J (((Quotient.out c : ↥D) : V ≃ₗ[K] V) x)
  have hU : tube D A 𝔭 J x = ⋃ c ∈ (Finset.univ : Finset (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D)), Ω c := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨g, hg, hy⟩
      refine ⟨QuotientGroup.mk (⟨g, hg⟩ : ↥D), ?_⟩
      rw [mem_tube_bot]
      have h1 := (quot_eq_iff (𝔭 := 𝔭) (J := J) (x := x) hD
        (Quotient.out (QuotientGroup.mk (⟨g, hg⟩ : ↥D) : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D))
        ⟨g, hg⟩).mp (Quotient.out_eq _)
      have := add_mem hy h1
      rwa [sub_add_sub_cancel] at this
    · rintro ⟨c, hc⟩
      exact ⟨_, (Quotient.out c : ↥D).2, mem_tube_bot.mp hc⟩
  rw [hU, cnt_biUnion h A 𝔭 k n hfink]
  · have hterm : ∀ c, cnt h A 𝔭 k n (Ω c) = cnt h A 𝔭 k n (tube ⊥ A 𝔭 J x) := by
      intro c
      have hg := hD (Quotient.out c : ↥D).2
      have h1 := cnt_gmap hg.1 A 𝔭 k n (tube ⊥ A 𝔭 J x)
      rw [hg.2] at h1
      rw [← h1]
      congr 1
      ext y
      rw [mem_tube_bot]
      constructor
      · intro hy
        refine ⟨((Quotient.out c : ↥D) : V ≃ₗ[K] V)⁻¹ y, ?_, ?_⟩
        · rw [mem_tube_bot]
          have := DA.apply_mem_smul (inv_mem hg).2 _ hy
          rwa [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app] at this
        · rw [← LinearEquiv.mul_apply, mul_inv_cancel, DA.one_app]
      · rintro ⟨z, hz, rfl⟩
        rw [← map_sub]
        exact DA.apply_mem_smul hg.2 _ (mem_tube_bot.mp hz)
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card]
    rfl
  · intro c _ y hy z hz
    rw [mem_tube_bot] at hy ⊢
    rw [add_sub_right_comm]
    exact add_mem hy (pow_smul_anti 𝔭 A hJk hz)
  · intro c _ c' _ hne
    rw [Set.disjoint_left]
    intro y hy hy'
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    refine (quot_eq_iff (𝔭 := 𝔭) (J := J) (x := x) hD _ _).mpr ?_
    have := sub_mem (mem_tube_bot.mp hy) (mem_tube_bot.mp hy')
    rwa [sub_sub_sub_cancel_left] at this

theorem cnt_tube_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    (hx : h x x = algebraMap F K (n : F))
    {J k : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ J) (hJk : J ≤ k)
    {C : Subgroup (V ≃ₗ[K] V)} (hC : C ≤ autSub h (locF 𝔭 A₀))
    (hΓ : ∀ g ∈ autSub h (locF 𝔭 A₀), (∀ z ∈ locF 𝔭 A₀,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • locF 𝔭 A₀ : Submodule (𝓞 K) V)) → g ∈ C) :
    cnt h (locF 𝔭 A₀) 𝔭 k n (tube (autSub h (locF 𝔭 A₀)) (locF 𝔭 A₀) 𝔭 J x) *
        C.relIndex (autSub h (locF 𝔭 A₀) ⊓ fixS x) =
      C.relIndex (autSub h (locF 𝔭 A₀)) * cnt h (locF 𝔭 A₀) 𝔭 k n (tube C (locF 𝔭 A₀) 𝔭 J x) := by
  set A := locF 𝔭 A₀ with hA
  have hidx := index_tube (autSub h A) (stabB h A 𝔭 J x) C (autSub h A ⊓ fixS x)
    (fun g hg => hg.1) hC
    (by
      rintro g ⟨hg, hgx⟩
      refine ⟨hg, ?_⟩
      rw [mem_fixS.mp hgx, sub_self]
      exact zero_mem _)
    (by
      rintro s ⟨hs1, hs2⟩
      have hsi := inv_mem hs1
      have hx' : h (s⁻¹ x) (s⁻¹ x) = algebraMap F K (n : F) := by rw [hsi.1, hx]
      have hd' : x - s⁻¹ x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
        have := DA.apply_mem_smul hsi.2 _ hs2
        rwa [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app] at this
      obtain ⟨γ, hγ1, hγ2, hγ3⟩ := exists_isom_congr hK hF hs hd hA₀ hA₀i h𝔭 hn
        (DA.apply_mem hsi.2 hxA) hxA hx' hx hJ hd'
      refine ⟨γ * s⁻¹, ⟨mul_mem hγ1 hsi, ?_⟩, ?_⟩
      · change (γ * s⁻¹) x = x
        rw [LinearEquiv.mul_apply, hγ3]
      · rw [inv_mul_cancel_right]
        exact hΓ γ hγ1 hγ2)
  rw [cnt_tube_eq hA₀ h𝔭 n hxA hJk le_rfl, cnt_tube_eq hA₀ h𝔭 n hxA hJk hC, mul_right_comm, hidx,
    mul_assoc]

theorem cnt_tube_refine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    (hx : h x x = algebraMap F K (n : F))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ J)
    {C : Subgroup (V ≃ₗ[K] V)} (hC : C ≤ autSub h (locF 𝔭 A₀))
    (hΓ : ∀ g ∈ autSub h (locF 𝔭 A₀), (∀ z ∈ locF 𝔭 A₀,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • locF 𝔭 A₀ : Submodule (𝓞 K) V)) → g ∈ C)
    {B : Submodule (𝓞 K) V} (hBA : B ≤ locF 𝔭 A₀) {r : ℕ}
    (hr : ((extP K 𝔭) ^ r • locF 𝔭 A₀ : Submodule (𝓞 K) V) ≤ B) {J₂ : ℕ} (hJ₂ : J ≤ J₂) :
    ∀ᶠ k in atTop, cnt h (locF 𝔭 A₀) 𝔭 k n (tube C (locF 𝔭 A₀) 𝔭 J x) =
      cnt h (locF 𝔭 A₀) 𝔭 k n (tube C B 𝔭 J₂ x) := by
  set A := locF 𝔭 A₀ with hA
  obtain ⟨c₀, hc₀⟩ := exists_exact_near hK hF hs hd hA₀ hA₀i h𝔭 hn ⟨x, hx⟩
  filter_upwards [eventually_ge_atTop (c₀ + (J₂ + r))] with k hk
  refine cnt_congr h A 𝔭 k n fun y hy hyn => ⟨?_, ?_⟩
  · rintro ⟨c, hc, hyc⟩
    obtain ⟨x', hx'A, hx', hx'y⟩ := hc₀ k (by omega) y hy hyn
    have hcA := hC hc
    have h1 : x' - c x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
      have := add_mem (pow_smul_anti 𝔭 A (show J ≤ k - c₀ by omega) hx'y) hyc
      rwa [sub_add_sub_cancel] at this
    obtain ⟨γ, hγ1, hγ2, hγ3⟩ := exists_isom_congr hK hF hs hd hA₀ hA₀i h𝔭 hn
      (DA.apply_mem hcA.2 hxA) hx'A (by rw [hcA.1, hx]) hx' hJ h1
    refine ⟨γ * c, mul_mem (hΓ γ hγ1 hγ2) hc, ?_⟩
    rw [LinearEquiv.mul_apply, hγ3, ← neg_sub]
    apply neg_mem
    have h2 := pow_smul_anti 𝔭 A (show J₂ + r ≤ k - c₀ by omega) hx'y
    rw [pow_add, mul_smul] at h2
    exact Submodule.smul_mono le_rfl hr h2
  · rintro ⟨c, hc, hyc⟩
    exact ⟨c, hc, pow_smul_anti 𝔭 A hJ₂ (Submodule.smul_mono le_rfl hBA hyc)⟩

theorem pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) {x : V} (hx : h x x = algebraMap F K (n : F)) (hx₁ : x ∈ locF 𝔭 M₁)
    (hx₂ : x ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      cnt h (locF 𝔭 M₁) 𝔭 k n (tube (autSub h (locF 𝔭 M₁)) (locF 𝔭 M₁) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 *
          (autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) *
          (autSub h (locF 𝔭 M₂) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₁) ⊓ fixS x) =
        cnt h (locF 𝔭 M₂) 𝔭 k n (tube (autSub h (locF 𝔭 M₂)) (locF 𝔭 M₂) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 *
          (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) *
          (autSub h (locF 𝔭 M₁) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₂) ⊓ fixS x) := by
  set A₁ := locF 𝔭 M₁ with hA₁
  set A₂ := locF 𝔭 M₂ with hA₂
  set C := autSub h A₁ ⊓ autSub h A₂ with hC
  set B := A₁ ⊓ A₂ with hB
  obtain ⟨j₁, hj₁⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  obtain ⟨j₂, hj₂⟩ := exists_congr_mem_autSub h hM₂ hM₁ h𝔭
  obtain ⟨r₁, hr₁⟩ := exists_pow_smul_le hM₁ hM₂ h𝔭
  obtain ⟨r₂, hr₂⟩ := exists_pow_smul_le hM₂ hM₁ h𝔭
  have hr₁' : ((extP K 𝔭) ^ r₁ • A₁ : Submodule (𝓞 K) V) ≤ B := le_inf Submodule.smul_le_right hr₁
  have hr₂' : ((extP K 𝔭) ^ r₂ • A₂ : Submodule (𝓞 K) V) ≤ B := le_inf hr₂ Submodule.smul_le_right
  have hlA₁ : locF 𝔭 A₁ = A₁ := LocalizedFibreSets.locF_idem 𝔭 M₁
  have hlA₂ : locF 𝔭 A₂ = A₂ := LocalizedFibreSets.locF_idem 𝔭 M₂
  have hlB : locF 𝔭 B = B := locF_inf h𝔭 hlA₁ hlA₂
  have hCB : ∀ g ∈ C, Formalism.HermitianLatticesTheory.gmap g B = B := by
    rintro g ⟨hg1, hg2⟩
    have e : Formalism.HermitianLatticesTheory.gmap g B = Formalism.HermitianLatticesTheory.gmap g A₁ ⊓ Formalism.HermitianLatticesTheory.gmap g A₂ :=
      Submodule.map_inf _ g.injective
    rw [e, hg1.2, hg2.2]
  filter_upwards [eventually_ge_atTop (4 * vF 𝔭 n + eA h A₁ 𝔭 + 1 + (4 * vF 𝔭 n + eA h A₂ 𝔭 + 1) +
    (j₁ + j₂ + 2 * vF 𝔭 n))] with J hJ
  have hJ₁ : 4 * vF 𝔭 n + eA h A₁ 𝔭 + 1 ≤ J := by omega
  have hJ₂ : 4 * vF 𝔭 n + eA h A₂ 𝔭 + 1 ≤ J := by omega
  have hΓ₁ : ∀ g ∈ autSub h A₁, (∀ z ∈ A₁,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • A₁ : Submodule (𝓞 K) V)) → g ∈ C :=
    fun g hg hz => ⟨hg, hj₁ _ (by omega) g hg hz⟩
  have hΓ₂ : ∀ g ∈ autSub h A₂, (∀ z ∈ A₂,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • A₂ : Submodule (𝓞 K) V)) → g ∈ C :=
    fun g hg hz => ⟨hj₂ _ (by omega) g hg hz, hg⟩
  filter_upwards [cnt_tube_refine hK hF hs hd hM₁ hM₁i h𝔭 hn hx₁ hx (J := J) hJ₁
      (C := C) inf_le_left hΓ₁ (B := B) inf_le_left hr₁' (le_refl J),
    cnt_tube_refine hK hF hs hd hM₂ hM₂i h𝔭 hn hx₂ hx (J := J) hJ₂
      (C := C) inf_le_right hΓ₂ (B := B) inf_le_right hr₂' (le_refl J),
    eventually_ge_atTop (J + r₁ + r₂)] with k hk₁ hk₂ hk
  have m₁ := cnt_tube_mul hK hF hs hd hM₁ hM₁i h𝔭 hn hx₁ hx (J := J) (k := k) hJ₁ (by omega)
    (C := C) inf_le_left hΓ₁
  have m₂ := cnt_tube_mul hK hF hs hd hM₂ hM₂i h𝔭 hn hx₂ hx (J := J) (k := k) hJ₂ (by omega)
    (C := C) inf_le_right hΓ₂
  rw [← hA₁] at m₁ hk₁
  rw [← hA₂] at m₂ hk₂
  rw [hk₁] at m₁
  rw [hk₂] at m₂

  have hΩB : tube C B 𝔭 J x ⊆ B := by
    rintro y ⟨g, hg, hy⟩
    have h1 : g x ∈ B := DA.apply_mem (hCB g hg) ⟨hx₁, hx₂⟩
    have := add_mem (Submodule.smul_le_right hy) h1
    rwa [sub_add_cancel] at this
  have hst : ∀ (A : Submodule (𝓞 K) V) (r : ℕ), ((extP K 𝔭) ^ r • A : Submodule (𝓞 K) V) ≤ B →
      J + r ≤ k → ∀ y ∈ tube C B 𝔭 J x, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V),
        y + z ∈ tube C B 𝔭 J x := by
    rintro A r hr hrk y ⟨g, hg, hy⟩ z hz
    refine ⟨g, hg, ?_⟩
    rw [add_sub_right_comm]
    refine add_mem hy ?_
    have h2 := pow_smul_anti 𝔭 A hrk hz
    rw [pow_add, mul_smul] at h2
    exact Submodule.smul_mono le_rfl hr h2
  have hle : ∀ (A : Submodule (𝓞 K) V) (r : ℕ), ((extP K 𝔭) ^ r • A : Submodule (𝓞 K) V) ≤ B →
      r ≤ k → ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ≤ B :=
    fun A r hr hrk => (pow_smul_anti 𝔭 A hrk).trans hr
  have hfinB := finite_quot_inf hM₁ hM₂ h𝔭 k
  have s₁ := cnt_sub hF (h := h) h𝔭 hlA₁ hlB (GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hM₁i) inf_le_left
    (hle A₁ r₁ hr₁' (by omega)) hfinB n hΩB (hst A₁ r₁ hr₁' (by omega))
  have s₂ := cnt_sub hF (h := h) h𝔭 hlA₂ hlB (GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hM₂i) inf_le_right
    (hle A₂ r₂ hr₂' (by omega)) hfinB n hΩB (hst A₂ r₂ hr₂' (by omega))
  have i0 := card_quot_inf_ne_zero hM₁ hM₂ h𝔭
  have im := card_quot_inf_mul hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭
  rw [← hA₁, ← hA₂, ← hB] at i0 im
  have hq : Ideal.absNorm 𝔭 ≠ 0 := (reductionMapsOfForms.absNorm_pos h𝔭).ne'

  have e1 : C.relIndex (autSub h A₁) = (autSub h A₂).relIndex (autSub h A₁) := by
    rw [hC, Subgroup.inf_relIndex_left]
  have e2 : C.relIndex (autSub h A₂) = (autSub h A₁).relIndex (autSub h A₂) := by
    rw [hC, Subgroup.inf_relIndex_right]
  have e3 : C.relIndex (autSub h A₁ ⊓ fixS x) =
      (autSub h A₂ ⊓ fixS x).relIndex (autSub h A₁ ⊓ fixS x) := by
    rw [← Subgroup.inf_relIndex_right C, ← Subgroup.inf_relIndex_right (autSub h A₂ ⊓ fixS x)]
    congr 1
    rw [hC]
    ac_rfl
  have e4 : C.relIndex (autSub h A₂ ⊓ fixS x) =
      (autSub h A₁ ⊓ fixS x).relIndex (autSub h A₂ ⊓ fixS x) := by
    rw [← Subgroup.inf_relIndex_right C, ← Subgroup.inf_relIndex_right (autSub h A₁ ⊓ fixS x)]
    congr 1
    rw [hC]
    ac_rfl
  rw [e1, e3] at m₁
  rw [e2, e4] at m₂
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero i0 (pow_ne_zero (vd h A₁ 𝔭) hq)))
  generalize cnt h A₁ 𝔭 k n (tube (autSub h A₁) A₁ 𝔭 J x) = E₁ at *
  generalize cnt h A₂ 𝔭 k n (tube (autSub h A₂) A₂ 𝔭 J x) = E₂ at *
  generalize cnt h A₁ 𝔭 k n (tube C B 𝔭 J x) = D₁ at *
  generalize cnt h A₂ 𝔭 k n (tube C B 𝔭 J x) = D₂ at *
  generalize cnt h B 𝔭 k n (tube C B 𝔭 J x) = W at *
  generalize Nat.card (↥A₁ ⧸ B.submoduleOf A₁) = i₁ at *
  generalize Nat.card (↥A₂ ⧸ B.submoduleOf A₂) = i₂ at *
  generalize Ideal.absNorm 𝔭 ^ vd h A₁ 𝔭 = Q₁ at *
  generalize Ideal.absNorm 𝔭 ^ vd h A₂ 𝔭 = Q₂ at *
  generalize (autSub h A₂).relIndex (autSub h A₁) = a at *
  generalize (autSub h A₁).relIndex (autSub h A₂) = b at *
  generalize (autSub h A₂ ⊓ fixS x).relIndex (autSub h A₁ ⊓ fixS x) = a' at *
  generalize (autSub h A₁ ⊓ fixS x).relIndex (autSub h A₂ ⊓ fixS x) = b' at *
  calc i₁ * Q₁ * (E₁ * Q₂ * b * a') = (E₁ * a') * i₁ * Q₁ * Q₂ * b := by ring
    _ = a * (i₁ * D₁) * Q₁ * Q₂ * b := by rw [m₁]; ring
    _ = a * (i₂ * D₂) * Q₁ * Q₂ * b := by rw [← s₁, s₂]
    _ = (b * D₂) * a * Q₁ * (i₂ * Q₂) := by ring
    _ = (E₂ * b') * a * Q₁ * (i₁ * Q₁) := by rw [← m₂, ← im]
    _ = i₁ * Q₁ * (E₂ * Q₁ * a * b') := by ring

end Formalism.HermitianLattices.Ext.L3.LIOrb
