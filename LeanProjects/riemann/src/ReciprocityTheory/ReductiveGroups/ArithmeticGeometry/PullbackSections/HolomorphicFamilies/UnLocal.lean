import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem valAt'_spMap {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = ψ a := by
  unfold valAt'
  rw [dif_pos (by simp)]
  unfold valAt
  have h1 : (spMap ψ).appLE ⊤ ⊤ (by simp) = (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | simp
  rw [h1]
  have h2 := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  refine h2.trans ?_
  simp

private lemma app_lemma_0 {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = ψ a := by
  have h0 := valAt'_spMap ψ a
  unfold valAt' at h0
  rw [dif_pos (by simp)] at h0
  unfold valAt at h0
  have h1 : (spMap ψ).appLE ⊤ ⊤ (by simp) = (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | simp
  rw [h1] at h0
  exact h0

private lemma vEq_lemma {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, V)) :
    valAt' (spMap ψ) V s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((spMap ψ).appLE V ⊤ e s) := by
  unfold valAt'
  rw [dif_pos e]
  rfl

private lemma preMono_lemma_8 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V W : (Sp A).Opens} (hVW : V ≤ W) :
    spMap ψ ⁻¹ᵁ V ≤ spMap ψ ⁻¹ᵁ W := by
  first
    | exact fun x hx => hVW hx
    | exact (Opens.map (spMap ψ).base).monotone hVW
    | exact Scheme.Hom.preimage_mono _ hVW
    | (intro x hx; exact hVW hx)

private lemma vRes_lemma_2 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V W : (Sp A).Opens} (hVW : V ≤ W)
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, W)) :
    valAt' (spMap ψ) V ((Sp A).presheaf.map (homOfLE hVW).op s) = valAt' (spMap ψ) W s := by
  rw [vEq_lemma ψ e, vEq_lemma ψ (e.trans (preMono_lemma_8 ψ hVW))]
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) s) ((spMap ψ).map_appLE e (homOfLE hVW).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom t) key

private lemma vMul_lemma_6 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s t : Γ(Sp A, V)) :
    valAt' (spMap ψ) V (s * t) = valAt' (spMap ψ) V s * valAt' (spMap ψ) V t := by
  simp only [vEq_lemma ψ e, map_mul]

private lemma vPow_lemma_7 {A : Type} [CommRing A] (ψ : A →+* ℂ) {V : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ V) (s : Γ(Sp A, V)) (n : ℕ) :
    valAt' (spMap ψ) V (s ^ n) = valAt' (spMap ψ) V s ^ n := by
  simp only [vEq_lemma ψ e, map_pow]

private lemma topLe_lemma_3 {A : Type} [CommRing A] (ψ : A →+* ℂ) (g : A) (hg : ψ g ≠ 0) :
    ⊤ ≤ spMap ψ ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) := by
  have hc := app_lemma_0 ψ g
  have hu : IsUnit ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)) := by
    have h0 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))) := by
      rw [hc]
      exact hg.isUnit
    have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h1
  have hb := (Sp ℂ).basicOpen_of_isUnit hu
  rw [Scheme.preimage_basicOpen]
  first
    | exact hb.symm.le
    | exact le_of_eq hb.symm
    | (rw [← Scheme.Hom.appTop, hb])
    | simp [Scheme.Hom.appTop, hb]

private lemma local_lemma_4 {A : Type} [CommRing A] (ψ : A →+* ℂ) {U : (Sp A).Opens}
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ U) : ∃ g : A, ψ g ≠ 0 ∧
      (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := by
    first
      | infer_instance
      | exact ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum ℂ)⟩
  have hpt : pt ∈ spMap ψ ⁻¹ᵁ U := e (show pt ∈ (⊤ : (Sp ℂ).Opens) by first | trivial | simp)
  obtain ⟨g', hD, hxD⟩ := (isAffineOpen_top (Sp A)).exists_basicOpen_le ⟨(spMap ψ).base pt, hpt⟩
    (by first | trivial | simp)
  obtain ⟨g, rfl⟩ : ∃ g : A, (Scheme.ΓSpecIso (CommRingCat.of A)).inv g = g' :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom g', by simp⟩
  refine ⟨g, ?_, hD⟩
  intro hg
  have hc := app_lemma_0 ψ g
  rw [hg] at hc
  have hc0 : (spMap ψ).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) = 0 := by
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hc
    simpa using h3
  have hpt' : pt ∈ spMap ψ ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) := hxD
  rw [Scheme.preimage_basicOpen] at hpt'
  first
    | rw [hc0] at hpt'
    | erw [hc0] at hpt'
    | rw [← Scheme.Hom.appTop, hc0] at hpt'
  first
    | (rw [Scheme.basicOpen_zero] at hpt'; simp at hpt')
    | (erw [Scheme.basicOpen_zero] at hpt'; simp at hpt')
    | (simp at hpt'; done)
    | exact absurd hpt' (by simp [Scheme.basicOpen_zero])
    | (rw [Scheme.mem_basicOpen] at hpt'; simp at hpt')
    | (erw [Scheme.mem_basicOpen] at hpt'; simp at hpt')

private lemma alg_lemma_5 {A : Type} [CommRing A] (ψ : A →+* ℂ) (g' : Γ(Sp A, ⊤))
    (e : ⊤ ≤ spMap ψ ⁻¹ᵁ (Sp A).basicOpen g') (x : Γ(Sp A, ⊤)) :
    valAt' (spMap ψ) ((Sp A).basicOpen g') (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen g') x) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) := by
  have h0 := vRes_lemma_2 ψ (le_top : (Sp A).basicOpen g' ≤ ⊤) e x
  have h2 := valAt'_spMap ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x)
  have hx : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) = x := by
    simp
  rw [hx] at h2
  exact h0.trans h2

theorem isHolTo_spMap {A : Type} [CommRing A] {m : ℕ} {B : Set (Fin m → ℂ)} (hB : IsOpen B) {Ψ : (Fin m → ℂ) → (A →+* ℂ)}
    (h : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) : IsHolTo B fun b => spMap (Ψ b) := by
  unfold IsHolTo
  intro U f
  have nbhd : ∀ b0 ∈ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U}, ∃ g : A, Ψ b0 g ≠ 0 ∧
      (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U :=
    fun b0 hb0 => local_lemma_4 (Ψ b0) hb0.2
  have hopen : ∀ g : A, IsOpen (B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ) :=
    fun g => ((h g).continuousOn).isOpen_inter_preimage hB isOpen_compl_singleton
  have hsub : ∀ g : A, (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) ≤ U →
      B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ ⊆ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U} := by
    intro g hD b hb
    exact ⟨hb.1, (topLe_lemma_3 (Ψ b) g hb.2).trans (preMono_lemma_8 (Ψ b) hD)⟩
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro b0 hb0
    obtain ⟨g, hg, hD⟩ := nbhd b0 hb0
    exact ⟨_, hsub g hD, hopen g, hb0.1, hg⟩
  · apply differentiableOn_of_locally_differentiableOn
    intro b0 hb0
    obtain ⟨g, hg, hD⟩ := nbhd b0 hb0
    refine ⟨_, hopen g, ⟨hb0.1, hg⟩, ?_⟩
    haveI := (isAffineOpen_top (Sp A)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g)
    obtain ⟨⟨h', m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
      ((Sp A).presheaf.map (homOfLE hD).op f)
    dsimp only at hm
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (Scheme.ΓSpecIso (CommRingCat.of A)).inv g ^ n = (m : Γ(Sp A, ⊤)) := by
      first
        | exact (Submonoid.mem_powers_iff _ _).mp m.2
        | exact m.2
        | simpa using m.2
        | (obtain ⟨k, hk⟩ := m.2; exact ⟨k, hk⟩)
    have key : ∀ b ∈ {b | b ∈ B ∧ ⊤ ≤ spMap (Ψ b) ⁻¹ᵁ U} ∩ (B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ),
        valAt' (spMap (Ψ b)) U f = Ψ b ((Scheme.ΓSpecIso (CommRingCat.of A)).hom h') * (Ψ b g ^ n)⁻¹ := by
      intro b hb
      have hgb : Ψ b g ≠ 0 := hb.2.2
      have eD := topLe_lemma_3 (Ψ b) g hgb
      rw [← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hgb), ← vRes_lemma_2 (Ψ b) hD eD f]
      have hm' := congrArg (valAt' (spMap (Ψ b)) _) hm
      rw [vMul_lemma_6 (Ψ b) eD, ← hn, map_pow, vPow_lemma_7 (Ψ b) eD, alg_lemma_5 (Ψ b) _ eD, alg_lemma_5 (Ψ b) _ eD] at hm'
      have hg' : (Scheme.ΓSpecIso (CommRingCat.of A)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) = g := by
        simp
      rw [hg'] at hm'
      exact hm'
    refine DifferentiableOn.congr ?_ key
    exact ((((h _).mono Set.inter_subset_left).mul ((((h g).mono Set.inter_subset_left).pow n).inv
      (fun b (hb : b ∈ B ∩ (fun b => Ψ b g) ⁻¹' {0}ᶜ) => pow_ne_zero n hb.2))).mono Set.inter_subset_right)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
