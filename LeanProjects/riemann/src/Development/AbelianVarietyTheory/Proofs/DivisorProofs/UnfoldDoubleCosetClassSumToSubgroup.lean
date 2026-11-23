import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.ClassSumUnfold

open Function

theorem finsum_eq_of_fiber {α β : Type} (Φ : α → β) (hΦ : Surjective Φ) (w : α → ℂ) (g : β → ℂ)
    (hfib : ∀ b, (Φ ⁻¹' {b}).Finite) (hw : (support w).Finite)
    (hwg : ∀ a, w a * ((Φ ⁻¹' {Φ a}).ncard : ℂ) = g (Φ a)) : ∑ᶠ a, w a = ∑ᶠ b, g b := by
  classical
  have hn : ∀ a, ((Φ ⁻¹' {Φ a}).ncard : ℂ) ≠ 0 := fun a => by
    have : 0 < (Φ ⁻¹' {Φ a}).ncard := (Set.ncard_pos (hfib _)).2 ⟨a, rfl⟩
    exact_mod_cast this.ne'
  have hw' : ∀ a, w a = g (Φ a) / ((Φ ⁻¹' {Φ a}).ncard : ℂ) := fun a => by
    rw [← hwg a, mul_div_cancel_right₀ _ (hn a)]
  set s := hw.toFinset with hs
  have hgs : support g ⊆ ↑(s.image Φ) := by
    intro b hb
    obtain ⟨a, rfl⟩ := hΦ b
    have : w a ≠ 0 := by
      intro h0; apply hb; rw [← hwg a, h0, zero_mul]
    rw [Finset.coe_image]
    exact ⟨a, by simpa [s] using this, rfl⟩
  rw [finsum_eq_sum_of_support_subset w (s := s) (by simp [s]), finsum_eq_sum_of_support_subset g hgs,
    ← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := s.image Φ) (fun i hi => Finset.mem_image_of_mem Φ hi)]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨a0, -, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.sum_congr rfl (fun a ha => by rw [hw' a, (Finset.mem_filter.1 ha).2]), Finset.sum_const, nsmul_eq_mul]
  by_cases hg : g (Φ a0) = 0
  · simp [hg]
  · have hfe : s.filter (fun a => Φ a = Φ a0) = (hfib (Φ a0)).toFinset := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, s,
        Function.mem_support]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [hw' a, h]
        exact div_ne_zero hg (by simpa [h] using hn a)
    rw [hfe, ← Set.ncard_eq_toFinset_card _ (hfib _)]
    field_simp [hn a0]

end GlobalTheory.ClassSumUnfold

namespace GlobalTheory.ClassSumUnfold

open Function

variable {G H : Type} [Group G] [Group H]

theorem mem_conj_iff (K : Subgroup G) (x g : G) :
    g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fiber_count (ι : H →* G) (hι : Injective ι) (Γ : Subgroup G) (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g)
    (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) (K : Subgroup G) (x : G)
    (hfin : Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) (δ₀ : H ⧸ T) :
    ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)}).Finite ∧
    ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)}).ncard *
      Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out
        (DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * x)))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  classical
  have hT : ∀ h, h ∈ T ↔ ι h ∈ Γ' := fun h => by
    rw [hΓ']
    exact ⟨fun h' => ⟨h, h', rfl⟩, fun ⟨t, ht, e⟩ => hι e ▸ ht⟩
  have hιΓ : ∀ h, ι h ∈ Γ := fun h => (hΓ _).2 ⟨h, rfl⟩
  have hΓ'Γ : ∀ g, g ∈ Γ' → g ∈ Γ := fun g hg => by
    obtain ⟨t, -, rfl⟩ := (hΓ' g).1 hg
    exact hιΓ t
  set S : Subgroup H := (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).comap ι with hSdef
  have hS : ∀ h, h ∈ S ↔ x⁻¹ * ι h * x ∈ K := fun h => by
    simp only [hSdef, Subgroup.mem_comap, Subgroup.mem_inf, mem_conj_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨hιΓ h, h'⟩⟩
  have hcardS : Nat.card S = Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
    rw [← Subgroup.card_map_of_injective (K := S) hι, hSdef, Subgroup.map_comap_eq]
    congr 2
    refine inf_eq_right.2 (fun g hg => ?_)
    obtain ⟨h, rfl⟩ := (hΓ g).1 (Subgroup.mem_inf.1 hg).1
    exact ⟨h, rfl⟩
  haveI : Finite S := Nat.finite_of_card_ne_zero (hcardS ▸ (Nat.card_pos).ne')
  set h₀ := Quotient.out δ₀ with hh₀
  have hδ₀ : ((h₀ : H) : H ⧸ T) = δ₀ := QuotientGroup.out_eq' δ₀
  have hsm : ∀ s : S, s • δ₀ = (((s : H) * h₀ : H) : H ⧸ T) := fun s => by
    rw [← hδ₀]
    first
    | rfl
    | simp [Subgroup.smul_def, MulAction.Quotient.smul_mk]
  have hfo : (fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * x)) ⁻¹'
      {DoubleCoset.mk Γ' K ((ι h₀)⁻¹ * x)} = MulAction.orbit S δ₀ := by
    ext δ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · intro he
      obtain ⟨g', hg', k, hk, e⟩ := (DoubleCoset.eq Γ' K _ _).1 he
      obtain ⟨t, ht, rfl⟩ := (hΓ' g').1 hg'
      have e' : (ι h₀)⁻¹ = ι t * ((ι (Quotient.out δ))⁻¹ * x) * k * x⁻¹ := by
        rw [← e]; group
      have hsK : x⁻¹ * ι (Quotient.out δ * t⁻¹ * h₀⁻¹) * x = k := by
        simp only [map_mul, map_inv]
        rw [e']; group
      refine ⟨⟨Quotient.out δ * t⁻¹ * h₀⁻¹, (hS _).2 (hsK ▸ hk)⟩, ?_⟩
      rw [hsm]
      conv_rhs => rw [← QuotientGroup.out_eq' δ]
      rw [QuotientGroup.eq]
      have : (Quotient.out δ * t⁻¹ * h₀⁻¹ * h₀)⁻¹ * Quotient.out δ = t := by group
      simp only [this]
      exact ht
    · rintro ⟨s, rfl⟩
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T ((s : H) * h₀)
      rw [hsm, ht, DoubleCoset.eq]
      refine ⟨ι t, (hT t).1 t.2, x⁻¹ * ι s * x, (hS s).1 s.2, ?_⟩
      simp only [map_mul, map_inv]
      group
  obtain ⟨g', k, hg', hk, hy⟩ := DoubleCoset.mk_out_eq_mul Γ' K ((ι h₀)⁻¹ * x)
  set y := Quotient.out (DoubleCoset.mk Γ' K ((ι h₀)⁻¹ * x)) with hydef
  set a := g' * (ι h₀)⁻¹ with hadef
  let φ : S →* G := (MulAut.conj a).toMonoidHom.comp (ι.comp S.subtype)
  have hφ : ∀ s : S, φ s = a * ι s * a⁻¹ := fun s => rfl
  have hφi : Injective φ := by
    intro s s' e
    rw [hφ, hφ] at e
    exact Subtype.ext (hι (by simpa using e))
  have hstab : ∀ s : S, s ∈ MulAction.stabilizer S δ₀ ↔ ι ((s : H) * h₀)⁻¹ * ι h₀ ∈ Γ' := fun s => by
    rw [MulAction.mem_stabilizer_iff, hsm]
    conv_lhs => rw [← hδ₀]
    rw [QuotientGroup.eq, hT, map_mul]
  have hmap : (MulAction.stabilizer S δ₀).map φ = Γ' ⊓ K.map (MulAut.conj y).toMonoidHom := by
    ext z
    rw [Subgroup.mem_inf, mem_conj_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' := (hstab s).1 hs
      have hsK := (hS s).1 s.2
      constructor
      · have : φ s = g' * (ι ((s : H) * h₀)⁻¹ * ι h₀)⁻¹ * g'⁻¹ := by
          rw [hφ]; simp only [hadef, map_mul, map_inv]; group
        rw [this]
        exact Γ'.mul_mem (Γ'.mul_mem hg' (Γ'.inv_mem hs')) (Γ'.inv_mem hg')
      · have : y⁻¹ * φ s * y = k⁻¹ * (x⁻¹ * ι s * x) * k := by
          rw [hφ, hy]; simp only [hadef]; group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem hk) hsK) hk
    · rintro ⟨hz1, hz2⟩
      have hΓz : a⁻¹ * z * a ∈ Γ := by
        simp only [hadef]
        exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (hΓ'Γ _ hg') (Γ.inv_mem (hιΓ h₀)))) (hΓ'Γ _ hz1))
          (Γ.mul_mem (hΓ'Γ _ hg') (Γ.inv_mem (hιΓ h₀)))
      obtain ⟨s, hs⟩ := (hΓ _).1 hΓz
      have hsS : s ∈ S := by
        rw [hS, hs]
        have : x⁻¹ * (a⁻¹ * z * a) * x = k * (y⁻¹ * z * y) * k⁻¹ := by
          rw [hy]; simp only [hadef]; group
        rw [this]
        exact K.mul_mem (K.mul_mem hk hz2) (K.inv_mem hk)
      refine ⟨⟨s, hsS⟩, (hstab _).2 ?_, ?_⟩
      · have : ι (s * h₀)⁻¹ * ι h₀ = g'⁻¹ * z⁻¹ * g' := by
          simp only [map_mul, map_inv]
          rw [hs]; simp only [hadef]; group
        rw [this]
        exact Γ'.mul_mem (Γ'.mul_mem (Γ'.inv_mem hg') (Γ'.inv_mem hz1)) hg'
      · rw [hφ]
        show a * ι s * a⁻¹ = z
        rw [hs]; group
  have hcst : Nat.card (MulAction.stabilizer S δ₀) = Nat.card ↥(Γ' ⊓ K.map (MulAut.conj y).toMonoidHom) := by
    rw [← hmap, Subgroup.card_map_of_injective hφi]
  refine ⟨?_, ?_⟩
  · rw [hfo]
    exact Set.finite_range _
  · rw [hfo, ← hcst, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index, hcardS]

end GlobalTheory.ClassSumUnfold

namespace GlobalTheory.ClassSumUnfold

open Function

theorem unfold_classSum : ∀ {G H : Type} [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h, ι h = g) → ∀ (T : Subgroup H) (Γ' : Subgroup G), (∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g) → ∀ (K : Subgroup G) (u : G → ℂ), (∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g) → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom)) → (∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) → ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) := by
  intro G H _ _ ι hι Γ hΓ T Γ' hΓ' K u hu hfinQ hfinS hsupp
  classical
  haveI := hfinQ
  have hιΓ : ∀ h, ι h ∈ Γ := fun h => (hΓ _).2 ⟨h, rfl⟩
  have hu' : ∀ g' ∈ Γ', ∀ k ∈ K, ∀ g, u (g' * g * k) = u g := by
    intro g' hg' k hk g
    obtain ⟨t, ht, rfl⟩ := (hΓ' g').1 hg'
    exact hu t ht k hk g
  let Φ : DoubleCoset.Quotient (Γ : Set G) (K : Set G) × (H ⧸ T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun p => DoubleCoset.mk Γ' K ((ι (Quotient.out p.2))⁻¹ * Quotient.out p.1)
  let w : DoubleCoset.Quotient (Γ : Set G) (K : Set G) × (H ⧸ T) → ℂ := fun p =>
    ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out p.1)).toMonoidHom) : ℂ))⁻¹ *
      u ((ι (Quotient.out p.2))⁻¹ * Quotient.out p.1)
  have hwfin : (support w).Finite := by
    refine ((Set.finite_univ (α := DoubleCoset.Quotient (Γ : Set G) (K : Set G))).prod
      (Set.finite_iUnion (fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) => hsupp (Quotient.out q)))).subset ?_
    rintro ⟨q, δ⟩ hp
    refine ⟨Set.mem_univ _, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    exact right_ne_zero_of_mul hp
  have hπ : ∀ q q' δ δ', Φ (q', δ) = Φ (q, δ') → q' = q := by
    intro q q' δ δ' h
    obtain ⟨g', hg', k, hk, e⟩ := (DoubleCoset.eq Γ' K _ _).1 h
    have hΓ'Γ : g' ∈ Γ := by
      obtain ⟨t, -, rfl⟩ := (hΓ' g').1 hg'
      exact hιΓ t
    rw [← DoubleCoset.out_eq' Γ K q, ← DoubleCoset.out_eq' Γ K q', DoubleCoset.eq]
    refine ⟨ι (Quotient.out δ') * g' * (ι (Quotient.out δ))⁻¹,
      Γ.mul_mem (Γ.mul_mem (hιΓ _) hΓ'Γ) (Γ.inv_mem (hιΓ _)), k, hk, ?_⟩
    have e' : Quotient.out q = ι (Quotient.out δ') * (g' * ((ι (Quotient.out δ))⁻¹ * Quotient.out q') * k) := by
      rw [← e]; group
    rw [e']; group
  have hsurj : Surjective Φ := by
    intro b
    obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K (Quotient.out b)
    obtain ⟨h, rfl⟩ := (hΓ γ).1 hγ
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T h
    refine ⟨(DoubleCoset.mk Γ K (Quotient.out b), (h : H ⧸ T)), ?_⟩
    show DoubleCoset.mk Γ' K ((ι (Quotient.out (h : H ⧸ T)))⁻¹ * Quotient.out (DoubleCoset.mk Γ K (Quotient.out b))) = b
    rw [ht, e]
    conv_rhs => rw [← DoubleCoset.out_eq' Γ' K b]
    rw [DoubleCoset.eq]
    refine ⟨ι t, (hΓ' _).2 ⟨t, t.2, rfl⟩, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [map_mul]
    group
  have hfib_eq : ∀ q δ₀, Φ ⁻¹' {Φ (q, δ₀)} = (fun δ => (q, δ)) ''
      ((fun δ : H ⧸ T => DoubleCoset.mk Γ' K ((ι (Quotient.out δ))⁻¹ * Quotient.out q)) ⁻¹'
        {DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q)}) := by
    intro q δ₀
    ext ⟨q', δ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro h
      have hq := hπ q q' δ δ₀ h
      subst hq
      exact ⟨δ, h, rfl⟩
    · rintro ⟨δ', hδ', he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact hδ'
  calc _ = ∑ᶠ p, w p := by
        rw [finsum_curry w hwfin]
        refine finsum_congr fun q => ?_
        rw [mul_finsum]
    _ = _ := by
      refine finsum_eq_of_fiber Φ hsurj w
        (fun b => ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out b)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out b))
        ?_ hwfin ?_
      · intro b
        obtain ⟨⟨q, δ₀⟩, rfl⟩ := hsurj b
        rw [hfib_eq]
        exact (fiber_count ι hι Γ hΓ T Γ' hΓ' K (Quotient.out q) (hfinS _) δ₀).1.image _
      · rintro ⟨q, δ₀⟩
        rw [hfib_eq, Set.ncard_image_of_injective _ (fun d d' e => by simpa using e)]
        obtain ⟨-, hc⟩ := fiber_count ι hι Γ hΓ T Γ' hΓ' K (Quotient.out q) (hfinS _) δ₀
        haveI := hfinS (Quotient.out q)
        have hS0 : Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) ≠ 0 := Nat.card_pos.ne'
        rw [← hc] at hS0
        obtain ⟨hn0, hc0⟩ := mul_ne_zero_iff.1 hS0
        obtain ⟨g', k, hg', hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q)
        have hue : u (Quotient.out (DoubleCoset.mk Γ' K ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q))) =
            u ((ι (Quotient.out δ₀))⁻¹ * Quotient.out q) := by rw [e, hu' g' hg' k hk]
        simp only [w, Φ]
        rw [hue, ← hc]
        push_cast
        field_simp

end GlobalTheory.ClassSumUnfold
